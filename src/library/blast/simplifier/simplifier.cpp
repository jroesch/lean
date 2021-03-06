/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <functional>
#include <iostream>
#include "util/flet.h"
#include "util/freset.h"
#include "util/pair.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/expr_lt.h"
#include "library/num.h"
#include "library/norm_num.h"
#include "library/attribute_manager.h"
#include "library/class_instance_resolution.h"
#include "library/relation_manager.h"
#include "library/app_builder.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/blast_exception.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/simplifier/simp_lemmas.h"
#include "library/blast/simplifier/ceqv.h"

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 1000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_TOP_DOWN
#define LEAN_DEFAULT_SIMPLIFY_TOP_DOWN false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE
#define LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_MEMOIZE
#define LEAN_DEFAULT_SIMPLIFY_MEMOIZE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL
#define LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS
#define LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_FUSE
#define LEAN_DEFAULT_SIMPLIFY_FUSE false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_NUMERALS
#define LEAN_DEFAULT_SIMPLIFY_NUMERALS false
#endif

namespace lean {
namespace blast {

using simp::result;

/* Keys */

static unsigned g_ac_key;
static unsigned g_som_key;
static unsigned g_numeral_key;

/* Options */

static name * g_simplify_max_steps     = nullptr;
static name * g_simplify_top_down      = nullptr;
static name * g_simplify_exhaustive    = nullptr;
static name * g_simplify_memoize       = nullptr;
static name * g_simplify_contextual    = nullptr;
static name * g_simplify_expand_macros = nullptr;
static name * g_simplify_fuse          = nullptr;
static name * g_simplify_numerals      = nullptr;

unsigned get_simplify_max_steps() {
    return ios().get_options().get_unsigned(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS);
}

bool get_simplify_top_down() {
    return ios().get_options().get_bool(*g_simplify_top_down, LEAN_DEFAULT_SIMPLIFY_TOP_DOWN);
}

bool get_simplify_exhaustive() {
    return ios().get_options().get_bool(*g_simplify_exhaustive, LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE);
}

bool get_simplify_memoize() {
    return ios().get_options().get_bool(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE);
}

bool get_simplify_contextual() {
    return ios().get_options().get_bool(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL);
}

bool get_simplify_expand_macros() {
    return ios().get_options().get_bool(*g_simplify_expand_macros, LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS);
}

bool get_simplify_fuse() {
    return ios().get_options().get_bool(*g_simplify_fuse, LEAN_DEFAULT_SIMPLIFY_FUSE);
}

bool get_simplify_numerals() {
    return ios().get_options().get_bool(*g_simplify_numerals, LEAN_DEFAULT_SIMPLIFY_NUMERALS);
}

/* Miscellaneous helpers */

static bool is_add_app(expr const & e) {
    return is_const_app(e, get_add_name(), 4);
}

static bool is_mul_app(expr const & e) {
    return is_const_app(e, get_mul_name(), 4);
}

static bool is_neg_app(expr const & e) {
    return is_const_app(e, get_neg_name(), 3);
}

/* Main simplifier class */

class simplifier {
    blast_tmp_type_context                       m_tmp_tctx;
    name                                         m_rel;
    expr_predicate                               m_simp_pred;

    simp_lemmas                                  m_srss;
    simp_lemmas                                  m_ctx_srss;

    /* Logging */
    unsigned                                     m_num_steps{0};

    /* Options */
    unsigned                                     m_max_steps{get_simplify_max_steps()};
    bool                                         m_top_down{get_simplify_top_down()};
    bool                                         m_exhaustive{get_simplify_exhaustive()};
    bool                                         m_memoize{get_simplify_memoize()};
    bool                                         m_contextual{get_simplify_contextual()};
    bool                                         m_expand_macros{get_simplify_expand_macros()};
    bool                                         m_fuse{get_simplify_fuse()};
    bool                                         m_numerals{get_simplify_numerals()};

    /* Cache */
    struct key {
        name              m_rel;
        expr              m_e;
        unsigned          m_hash;

        key(name const & rel, expr const & e):
            m_rel(rel), m_e(e), m_hash(hash(rel.hash(), abstract_hash(e))) { }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.m_hash; }
    };

    struct key_eq_fn {
        bool operator()(key const & k1, key const & k2) const {
            return k1.m_rel == k2.m_rel && abstract_is_equal(k1.m_e, k2.m_e);
        }
    };

    typedef std::unordered_map<key, result, key_hash_fn, key_eq_fn> simplify_cache;
    simplify_cache m_cache;
    optional<result> cache_lookup(expr const & e);
    void cache_save(expr const & e, result const & r);

    /* Mapping from subsingleton type to representative */
    expr_map<expr> m_subsingleton_elem_map;
    optional<result> normalize_subsingleton_args(expr const & e);

    /* Basic helpers */
    bool using_eq() { return m_rel == get_eq_name(); }

    bool is_dependent_fn(expr const & f) {
        expr f_type = m_tmp_tctx->whnf(m_tmp_tctx->infer(f));
        lean_assert(is_pi(f_type));
        return has_free_vars(binding_body(f_type));
    }

    simp_lemmas add_to_srss(simp_lemmas const & _srss, buffer<expr> & ls) {
        simp_lemmas srss = _srss;
        for (unsigned i = 0; i < ls.size(); i++) {
            expr & l = ls[i];
            blast_tmp_type_context tctx;
            try {
                // TODO(Leo,Daniel): should we allow the user to set the priority of local lemmas
                srss = add(*tctx, srss, mlocal_name(l), tctx->infer(l), l, LEAN_DEFAULT_PRIORITY);
            } catch (exception e) {
            }
        }
        return srss;
    }

    expr unfold_reducible_instances(expr const & e);
    expr remove_unnecessary_casts(expr const & e);

    bool instantiate_emetas(blast_tmp_type_context & tmp_tctx, unsigned num_emeta,
                            list<expr> const & emetas, list<bool> const & instances);

    /* Results */
    result lift_from_eq(expr const & e_old, result const & r_eq);
    result join(result const & r1, result const & r2);
    result funext(result const & r, expr const & l);
    result finalize(result const & r);

    /* Simplification */
    result simplify(expr const & e, simp_lemmas const & srss);
    result simplify(expr const & e, bool is_root);
    result simplify_lambda(expr const & e);
    result simplify_pi(expr const & e);
    result simplify_app(expr const & e);
    result simplify_fun(expr const & e);
    optional<result> simplify_numeral(expr const & e);

    /* Proving */
    optional<expr> prove(expr const & thm);
    optional<expr> prove(expr const & thm, simp_lemmas const & srss);

    /* Rewriting */
    result rewrite(expr const & e);
    result rewrite(expr const & e, simp_lemmas const & srss);
    result rewrite(expr const & e, simp_lemma const & sr);

    /* Congruence */
    result congr_fun_arg(result const & r_f, result const & r_arg);
    result congr(result const & r_f, result const & r_arg);
    result congr_fun(result const & r_f, expr const & arg);
    result congr_arg(expr const & f, result const & r_arg);
    result congr_funs(result const & r_f, buffer<expr> const & args);

    result try_congrs(expr const & e);
    result try_congr(expr const & e, user_congr_lemma const & cr);

    template<typename F>
    optional<result> synth_congr(expr const & e, F && simp);

    /* Fusion */
    result maybe_fuse(expr const & e, bool is_root);
    result fuse(expr const & e);
    expr_pair split_summand(expr const & e, expr const & f_mul, expr const & one);

    /* Apply whnf and eta-reduction
       \remark We want (Sum n (fun x, f x)) and (Sum n f) to be the same.
       \remark We may want to switch to eta-expansion later (see paper: "The Virtues of Eta-expansion").
       TODO(Daniel, Leo): should we add an option for disabling/enabling eta? */
    expr whnf_eta(expr const & e);

public:
    simplifier(name const & rel, expr_predicate const & simp_pred): m_rel(rel), m_simp_pred(simp_pred) { }
    result operator()(expr const & e, simp_lemmas const & srss)  { return simplify(e, srss); }
};

/* Cache */

optional<result> simplifier::cache_lookup(expr const & e) {
    /* cache_lookup is based on congr_lemma, and assumes \c e is an application */
    if (!is_app(e)) return optional<result>();
    auto it = m_cache.find(key(m_rel, e));
    if (it == m_cache.end()) return optional<result>();
    /* The cache ignores subsingletons, so we may need to
       synthesize a congruence lemma. */
    expr e_old = it->first.m_e;
    result r_old = it->second;
    lean_assert(abstract_is_equal(e, e_old));
    if (e == e_old) return optional<result>(r_old);
    lean_assert(is_app(e_old));
    buffer<expr> new_args, old_args;
    DEBUG_CODE(expr const & f_new =) get_app_args(e, new_args);
    DEBUG_CODE(expr const & f_old =) get_app_args(e_old, old_args);
    lean_assert(f_new == f_old);
    auto congr_lemma = mk_specialized_congr_lemma(e);
    if (!congr_lemma) return optional<result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();

    unsigned i = 0;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            lean_assert(ckind == congr_arg_kind::Cast || new_args[i] == old_args[i], static_cast<unsigned>(ckind), new_args[i], old_args[i]);
            expr rfl;
            switch (ckind) {
            case congr_arg_kind::HEq:
                lean_unreachable();
            case congr_arg_kind::Fixed:
                proof = mk_app(proof, new_args[i]);
                type = instantiate(binding_body(type), new_args[i]);
                break;
            case congr_arg_kind::FixedNoParam:
                break;
            case congr_arg_kind::Eq:
                proof = mk_app(proof, new_args[i]);
                type = instantiate(binding_body(type), new_args[i]);
                rfl = get_app_builder().mk_eq_refl(old_args[i]);
                proof = mk_app(proof, old_args[i], rfl);
                type = instantiate(binding_body(type), old_args[i]);
                type = instantiate(binding_body(type), rfl);
                break;
            case congr_arg_kind::Cast:
                proof = mk_app(proof, new_args[i]);
                type = instantiate(binding_body(type), new_args[i]);
                proof = mk_app(proof, old_args[i]);
                type = instantiate(binding_body(type), old_args[i]);
                break;
            }
            i++;
        });

    lean_assert(is_eq(type));
    result r_congr = result(e_old, proof);
    return optional<result>(join(r_congr, r_old));
}

void simplifier::cache_save(expr const & e, result const & r) {
    m_cache.insert(mk_pair(key(m_rel, e), r));
}

/* Results */

result simplifier::lift_from_eq(expr const & e_old, result const & r_eq) {
    if (!r_eq.has_proof()) return r_eq;
    lean_assert(r_eq.has_proof());
    /* r_eq.get_proof() : e_old = r_eq.get_new() */
    /* goal : e_old <m_rel> r_eq.get_new() */
    expr l = m_tmp_tctx->mk_tmp_local(m_tmp_tctx->infer(e_old));
    expr motive_local = get_app_builder().mk_app(m_rel, e_old, l);
    /* motive = fun y, e_old <m_rel> y */
    expr motive = Fun(l, motive_local);
    /* Rxx = x <m_rel> x */
    expr Rxx = get_app_builder().mk_refl(m_rel, e_old);
    expr pf = get_app_builder().mk_eq_rec(motive, Rxx, r_eq.get_proof());
    return result(r_eq.get_new(), pf);
}

result simplifier::join(result const & r1, result const & r2) {
    /* Assumes that both results are with respect to the same relation */
    if (!r1.has_proof()) {
        return r2;
    } else if (!r2.has_proof()) {
        lean_assert(r1.has_proof());
        return result(r2.get_new(), r1.get_proof());
    } else {
        /* If they both have proofs, we need to glue them together with transitivity. */
        lean_assert(r1.has_proof() && r2.has_proof());
        expr trans = get_app_builder().mk_trans(m_rel, r1.get_proof(), r2.get_proof());
        return result(r2.get_new(), trans);
    }
}

result simplifier::funext(result const & r, expr const & l) {
    // theorem funext {f₁ f₂ : Πx : A, B x} : (∀x, f₁ x = f₂ x) → f₁ = f₂ :=
    expr e  = Fun(l, r.get_new());
    if (!r.has_proof()) return result(e);
    expr pf = get_app_builder().mk_app(get_funext_name(), Fun(l, r.get_proof()));
    return result(e, pf);
}

result simplifier::finalize(result const & r) {
    if (r.has_proof()) return r;
    expr pf = get_app_builder().mk_refl(m_rel, r.get_new());
    return result(r.get_new(), pf);
}

/* Whnf + Eta */
expr simplifier::whnf_eta(expr const & e) {
    return try_eta(whnf(e));
}

/* Simplification */

result simplifier::simplify(expr const & e, simp_lemmas const & srss) {
    flet<simp_lemmas> set_srss(m_srss, srss);
    freset<simplify_cache> reset1(m_cache);
    freset<expr_map<expr>> reset2(m_subsingleton_elem_map);
    return simplify(e, true);
}

result simplifier::simplify(expr const & e, bool is_root) {
    check_system("simplifier");
    m_num_steps++;
    lean_trace_inc_depth("simplifier");
    lean_trace_d("simplifier", tout() << m_rel << ": " << ppb(e) << "\n";);

    if (m_num_steps > m_max_steps)
        throw blast_exception("simplifier failed, maximum number of steps exceeded", e);

    if (m_memoize) {
        if (auto it = cache_lookup(e)) return *it;
    }

    if (!m_simp_pred(e)) return result(e);

    if (m_numerals && using_eq()) {
        if (auto r = simplify_numeral(e)) {
            return *r;
        }
    }

    result r(e);

    if (m_top_down) r = join(r, rewrite(whnf_eta(r.get_new())));

    r.update(whnf_eta(r.get_new()));

    switch (r.get_new().kind()) {
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Constant:
        // no-op
        break;
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Macro:
        if (m_expand_macros) {
            if (auto m = m_tmp_tctx->expand_macro(e)) r = join(r, simplify(whnf_eta(*m), is_root));
        }
        break;
    case expr_kind::Lambda:
        if (using_eq()) r = join(r, simplify_lambda(r.get_new()));
        break;
    case expr_kind::Pi:
        r = join(r, simplify_pi(r.get_new()));
        break;
    case expr_kind::App:
        r = join(r, simplify_app(r.get_new()));
        break;
    }

    if (!m_top_down) r = join(r, rewrite(whnf_eta(r.get_new())));

    if (r.get_new() == e && !using_eq()) {
        result r_eq;
        {
            flet<name> use_eq(m_rel, get_eq_name());
            r_eq = simplify(r.get_new(), is_root);
        }
        r = join(r, lift_from_eq(r.get_new(), r_eq));
    }

    if (m_exhaustive && r.has_proof()) r = join(r, simplify(r.get_new(), is_root));

    if (m_memoize) cache_save(e, r);

    if (m_fuse && using_eq()) r = join(r, maybe_fuse(r.get_new(), is_root));

    return r;
}

result simplifier::simplify_lambda(expr const & e) {
    lean_assert(is_lambda(e));
    expr t = e;

    buffer<expr> ls;
    while (is_lambda(t)) {
        expr d = instantiate_rev(binding_domain(t), ls.size(), ls.data());
        expr l = m_tmp_tctx->mk_tmp_local(binding_name(t), d, binding_info(t));
        ls.push_back(l);
        t = instantiate(binding_body(t), l);
    }

    result r        = simplify(t, false);
    expr new_t      = r.get_new();
    /* check if subsingleton, and normalize */
    expr new_t_type = m_tmp_tctx->infer(new_t);
    if (m_tmp_tctx->mk_subsingleton_instance(new_t_type)) {
        auto it = m_subsingleton_elem_map.find(new_t_type);
        if (it != m_subsingleton_elem_map.end()) {
            if (it->second != new_t) {
                expr proof = get_app_builder().mk_app(get_subsingleton_elim_name(), new_t, it->second);
                r = join(r, result(it->second, proof));
            }
        } else {
            m_subsingleton_elem_map.insert(mk_pair(new_t_type, new_t));
        }
    }

    for (int i = ls.size() - 1; i >= 0; --i) r = funext(r, ls[i]);
    return r;
}

result simplifier::simplify_pi(expr const & e) {
    lean_assert(is_pi(e));
    return try_congrs(e);
}

expr simplifier::unfold_reducible_instances(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    fun_info f_info = get_specialized_fun_info(e);
    int i = -1;
    for_each(f_info.get_params_info(), [&](param_info const & p_info) {
            i++;
            if (p_info.is_inst_implicit() && !p_info.is_subsingleton()) {
                args[i] = blast::normalize(args[i]);
            }
        });
    return mk_app(f, args);
}

result simplifier::simplify_app(expr const & _e) {
    lean_assert(is_app(_e));
    expr e = unfold_reducible_instances(_e);

    /* (1) Try user-defined congruences */
    result r_user = try_congrs(e);
    if (r_user.has_proof()) {
        if (using_eq()) return join(r_user, simplify_fun(r_user.get_new()));
        else return r_user;
    }

    /* (2) Synthesize congruence lemma */
    if (using_eq()) {
        optional<result> r_args = synth_congr(e, [&](expr const & e) {
                return simplify(e, false);
            });
        if (r_args) return join(*r_args, simplify_fun(r_args->get_new()));
    }

    /* (3) Fall back on generic binary congruence */
    if (using_eq()) {
        expr const & f = app_fn(e);
        expr const & arg = app_arg(e);

        // TODO(dhs): it is not clear if this recursive call should be considered
        // a root or not, though does not matter since if + were being applied,
        // we would have synthesized a congruence rule in step (2).
        result r_f = simplify(f, false);

        if (is_dependent_fn(f)) {
            if (r_f.has_proof()) return congr_fun(r_f, arg);
            else return mk_app(r_f.get_new(), arg);
        } else {
            result r_arg = simplify(arg, false);
            return congr_fun_arg(r_f, r_arg);
        }
    }
    return result(e);
}

result simplifier::simplify_fun(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    result r_f = simplify(f, true);
    return congr_funs(r_f, args);
}

optional<result> simplifier::simplify_numeral(expr const & e) {
    if (is_num(e)) { return optional<result>(result(e)); }

    try {
        expr_pair r = mk_norm_num(*m_tmp_tctx, e);
        return optional<result>(result(r.first, r.second));
    } catch (exception e) {
        return optional<result>();
    }
}

/* Proving */

optional<expr> simplifier::prove(expr const & thm) {
    flet<name> set_name(m_rel, get_iff_name());
    result r_cond = simplify(thm, true);
    if (is_constant(r_cond.get_new()) && const_name(r_cond.get_new()) == get_true_name()) {
        expr pf = get_app_builder().mk_app(get_iff_elim_right_name(),
                                       finalize(r_cond).get_proof(),
                                       mk_constant(get_true_intro_name()));
        return some_expr(pf);
    }
    return none_expr();
}

optional<expr> simplifier::prove(expr const & thm, simp_lemmas const & srss) {
    flet<name> set_name(m_rel, get_iff_name());
    result r_cond = simplify(thm, srss);
    if (is_constant(r_cond.get_new()) && const_name(r_cond.get_new()) == get_true_name()) {
        expr pf = get_app_builder().mk_app(get_iff_elim_right_name(),
                                       finalize(r_cond).get_proof(),
                                       mk_constant(get_true_intro_name()));
        return some_expr(pf);
    }
    return none_expr();
}

/* Rewriting */

result simplifier::rewrite(expr const & e) {
    result r(e);
    while (true) {
        result r_ctx = rewrite(r.get_new(), m_ctx_srss);
        result r_new = rewrite(r_ctx.get_new(), m_srss);
        if (!r_ctx.has_proof() && !r_new.has_proof()) break;
        r = join(join(r, r_ctx), r_new);
    }
    return r;
}

result simplifier::rewrite(expr const & e, simp_lemmas const & srss) {
    result r(e);

    simp_lemmas_for const * sr = srss.find(m_rel);
    if (!sr) return r;

    list<simp_lemma> const * srs = sr->find_simp(e);
    if (!srs) return r;

    for_each(*srs, [&](simp_lemma const & sr) {
            result r_new = rewrite(r.get_new(), sr);
            if (!r_new.has_proof()) return;
            r = join(r, r_new);
        });
    return r;
}

result simplifier::rewrite(expr const & e, simp_lemma const & sr) {
    blast_tmp_type_context tmp_tctx(sr.get_num_umeta(), sr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e, sr.get_lhs())) return result(e);

    lean_trace(name({"simplifier", "rewrite"}),
               expr new_lhs = tmp_tctx->instantiate_uvars_mvars(sr.get_lhs());
               expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sr.get_rhs());
               tout() << "(" << sr.get_id() << ") "
               << "[" << ppb(new_lhs) << " --> " << ppb(new_rhs) << "]\n";);

    if (!instantiate_emetas(tmp_tctx, sr.get_num_emeta(), sr.get_emetas(), sr.get_instances())) return result(e);

    for (unsigned i = 0; i < sr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }

    expr new_lhs = tmp_tctx->instantiate_uvars_mvars(sr.get_lhs());
    expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sr.get_rhs());

    if (sr.is_perm()) {
        if (!is_light_lt(new_rhs, new_lhs))
            return result(e);
    }

    expr pf = tmp_tctx->instantiate_uvars_mvars(sr.get_proof());
    return result(new_rhs, pf);
}

/* Congruence */

result simplifier::congr_fun_arg(result const & r_f, result const & r_arg) {
    if (!r_f.has_proof() && !r_arg.has_proof()) return result(mk_app(r_f.get_new(), r_arg.get_new()));
    else if (!r_f.has_proof()) return congr_arg(r_f.get_new(), r_arg);
    else if (!r_arg.has_proof()) return congr_fun(r_f, r_arg.get_new());
    else return congr(r_f, r_arg);
}

result simplifier::congr(result const & r_f, result const & r_arg) {
    lean_assert(r_f.has_proof() && r_arg.has_proof());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e  = mk_app(r_f.get_new(), r_arg.get_new());
    expr pf = get_app_builder().mk_congr(r_f.get_proof(), r_arg.get_proof());
    return result(e, pf);
}

result simplifier::congr_fun(result const & r_f, expr const & arg) {
    lean_assert(r_f.has_proof());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e  = mk_app(r_f.get_new(), arg);
    expr pf = get_app_builder().mk_congr_fun(r_f.get_proof(), arg);
    return result(e, pf);
}

result simplifier::congr_arg(expr const & f, result const & r_arg) {
    lean_assert(r_arg.has_proof());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e  = mk_app(f, r_arg.get_new());
    expr pf = get_app_builder().mk_congr_arg(f, r_arg.get_proof());
    return result(e, pf);
}

/* Note: handles reflexivity */
result simplifier::congr_funs(result const & r_f, buffer<expr> const & args) {
    // congr_fun : ∀ {A : Type} {B : A → Type} {f g : Π (x : A), B x}, f = g → (∀ (a : A), f a = g a)
    expr e = r_f.get_new();
    for (unsigned i = 0; i < args.size(); ++i) {
        e  = mk_app(e, args[i]);
    }
    if (!r_f.has_proof()) return result(e);
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        pf = get_app_builder().mk_app(get_congr_fun_name(), pf, args[i]);
    }
    return result(e, pf);
}

result simplifier::try_congrs(expr const & e) {
    simp_lemmas_for const * sr = get_simp_lemmas().find(m_rel);
    if (!sr) return result(e);

    list<user_congr_lemma> const * crs = sr->find_congr(e);
    if (!crs) return result(e);

    result r(e);
    for_each(*crs, [&](user_congr_lemma const & cr) {
            if (r.has_proof()) return;
            r = try_congr(e, cr);
        });
    return r;
}

result simplifier::try_congr(expr const & e, user_congr_lemma const & cr) {
    blast_tmp_type_context tmp_tctx(cr.get_num_umeta(), cr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e, cr.get_lhs())) return result(e);

    lean_trace(name({"simplifier", "congruence"}),
               expr new_lhs = tmp_tctx->instantiate_uvars_mvars(cr.get_lhs());
               expr new_rhs = tmp_tctx->instantiate_uvars_mvars(cr.get_rhs());
               diagnostic(env(), ios())
               << "(" << cr.get_id() << ") "
               << "[" << ppb(new_lhs) << " =?= " << ppb(new_rhs) << "]\n";);

    /* First, iterate over the congruence hypotheses */
    bool failed = false;
    bool simplified = false;
    list<expr> const & congr_hyps = cr.get_congr_hyps();
    for_each(congr_hyps, [&](expr const & m) {
            if (failed) return;
            buffer<expr> ls;
            expr m_type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));

            while (is_pi(m_type)) {
                expr d = instantiate_rev(binding_domain(m_type), ls.size(), ls.data());
                expr l = tmp_tctx->mk_tmp_local(d, binding_info(m_type));
                lean_assert(!has_metavar(l));
                ls.push_back(l);
                m_type = instantiate(binding_body(m_type), l);
            }

            expr h_rel, h_lhs, h_rhs;
            lean_verify(is_simp_relation(env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel));
            {
                flet<name> set_name(m_rel, const_name(h_rel));

                flet<simp_lemmas> set_ctx_srss(m_ctx_srss, m_contextual ? add_to_srss(m_ctx_srss, ls) : m_ctx_srss);

                h_lhs = tmp_tctx->instantiate_uvars_mvars(h_lhs);
                lean_assert(!has_metavar(h_lhs));

                result r_congr_hyp = simplify(h_lhs, m_srss);
                if (r_congr_hyp.has_proof()) simplified = true;
                r_congr_hyp = finalize(r_congr_hyp);
                expr hyp = finalize(r_congr_hyp).get_proof();

                if (!tmp_tctx->is_def_eq(m, Fun(ls, hyp))) failed = true;
            }
        });

    if (failed || !simplified) return result(e);

    if (!instantiate_emetas(tmp_tctx, cr.get_num_emeta(), cr.get_emetas(), cr.get_instances())) return result(e);

    for (unsigned i = 0; i < cr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }

    expr e_s = tmp_tctx->instantiate_uvars_mvars(cr.get_rhs());
    expr pf = tmp_tctx->instantiate_uvars_mvars(cr.get_proof());
    return result(e_s, pf);
}

bool simplifier::instantiate_emetas(blast_tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas,
                                    list<bool> const & instances) {
    bool failed = false;
    unsigned i = num_emeta;
    for_each2(emetas, instances, [&](expr const & m, bool const & is_instance) {
            i--;
            if (failed) return;
            expr m_type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));
            lean_assert(!has_metavar(m_type));

            if (tmp_tctx->is_mvar_assigned(i)) return;

            if (is_instance) {
                if (auto v = tmp_tctx->mk_class_instance(m_type)) {
                    if (!tmp_tctx->assign(m, *v)) {
                        lean_trace(name({"simplifier", "failure"}),
                                   tout() << "unable to assign instance for: " << ppb(m_type) << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_trace(name({"simplifier", "failure"}),
                               tout() << "unable to synthesize instance for: " << ppb(m_type) << "\n";);
                    failed = true;
                    return;
                }
            }

            if (tmp_tctx->is_mvar_assigned(i)) return;

            if (tmp_tctx->is_prop(m_type)) {
                if (auto pf = prove(m_type)) {
                    lean_verify(tmp_tctx->is_def_eq(m, *pf));
                    return;
                }
            }

            lean_trace(name({"simplifier", "failure"}),
                       tout() << "failed to assign: " << m << " : " << ppb(m_type) << "\n";);

            failed = true;
            return;
        });

    return !failed;
}

/* Given a function application \c e, replace arguments that are subsingletons with a
   representative */
optional<result> simplifier::normalize_subsingleton_args(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr_lemma(e);
    if (!congr_lemma) return optional<result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    unsigned i = 0;
    bool normalized = false;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            expr rfl;
            switch (ckind) {
            case congr_arg_kind::HEq:
                lean_unreachable();
            case congr_arg_kind::Fixed:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                break;
            case congr_arg_kind::FixedNoParam:
                break;
            case congr_arg_kind::Eq:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                rfl = get_app_builder().mk_eq_refl(args[i]);
                proof = mk_app(proof, args[i], rfl);
                type = instantiate(binding_body(type), args[i]);
                type = instantiate(binding_body(type), rfl);
                break;
            case congr_arg_kind::Cast:
                proof = mk_app(proof, args[i]);
                type  = instantiate(binding_body(type), args[i]);
                expr const & arg_type = binding_domain(type);
                expr new_arg;
                auto it = m_subsingleton_elem_map.find(arg_type);
                if (it != m_subsingleton_elem_map.end()) {
                    normalized = (it->second != args[i]);
                    new_arg    = it->second;
                } else {
                    new_arg = args[i];
                    m_subsingleton_elem_map.insert(mk_pair(arg_type, args[i]));
                }
                proof = mk_app(proof, new_arg);
                type = instantiate(binding_body(type), new_arg);
                break;
            }
            i++;
        });
    if (!normalized) return optional<result>();
    lean_assert(is_eq(type));
    buffer<expr> type_args;
    get_app_args(type, type_args);
    expr e_new = type_args[2];
    return optional<result>(result(e_new, proof));
}

template<typename F>
optional<result> simplifier::synth_congr(expr const & e, F && simp) {
    static_assert(std::is_same<typename std::result_of<F(expr const & e)>::type, result>::value,
                  "synth_congr: simp must take expressions to results");
    lean_assert(is_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr_lemma_for_simp(e);
    if (!congr_lemma) return optional<result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    unsigned i = 0;
    bool has_proof              = false;
    bool has_cast               = false;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            switch (ckind) {
            case congr_arg_kind::HEq:
                lean_unreachable();
            case congr_arg_kind::Fixed:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                break;
            case congr_arg_kind::FixedNoParam:
                break;
            case congr_arg_kind::Eq:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                {
                    result r_arg = simp(args[i]);
                    if (r_arg.has_proof()) has_proof = true;
                    r_arg = finalize(r_arg);
                    proof = mk_app(proof, r_arg.get_new(), r_arg.get_proof());
                    type = instantiate(binding_body(type), r_arg.get_new());
                    type = instantiate(binding_body(type), r_arg.get_proof());
                }
                break;
            case congr_arg_kind::Cast:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                has_cast = true;
                break;
            }
            i++;
        });
    lean_assert(is_eq(type));
    buffer<expr> type_args;
    get_app_args(type, type_args);
    expr e_new = remove_unnecessary_casts(type_args[2]);
    result r;
    if (has_proof) r = result(e_new, proof);
    else r = result(e_new);

    if (has_cast) {
        if (auto r_norm = normalize_subsingleton_args(e_new))
            r = join(r, *r_norm);
    }
    return optional<result>(r);
}

expr simplifier::remove_unnecessary_casts(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    fun_info f_info = get_specialized_fun_info(e);
    int i = -1;
    for_each(f_info.get_params_info(), [&](param_info const & p_info) {
            i++;
            if (p_info.is_subsingleton()) {
                while (is_constant(get_app_fn(args[i]))) {
                    buffer<expr> cast_args;
                    expr f_cast = get_app_args(args[i], cast_args);
                    name n_f = const_name(f_cast);
                    if (n_f == get_eq_rec_name() || n_f == get_eq_drec_name() || n_f == get_eq_nrec_name()) {
                        lean_assert(cast_args.size() == 6);
                        expr major_premise = cast_args[5];
                        expr f_major_premise = get_app_fn(major_premise);
                        if (is_constant(f_major_premise) && const_name(f_major_premise) == get_eq_refl_name())
                            args[i] = cast_args[3];
                        else
                            return;
                    } else {
                        return;
                    }
                }
            }
        });
    return mk_app(f, args);
}

/* Fusion */

result simplifier::maybe_fuse(expr const & e, bool is_root) {
    if (!is_app(e)) return result(e);
    if (is_root && is_add_app(e)) return fuse(e);
    if (!is_root && is_add_app(e)) return result(e);
    lean_assert(!is_add_app(e));
    /* At this point we know we are an application of something other than + */
    optional<result> r = synth_congr(e, [&](expr const & arg) {
            if (is_add_app(arg)) return fuse(arg);
            else return result(arg);
        });
    if (r) return *r;
    else return result(e);
}

result simplifier::fuse(expr const & e) {
    lean_assert(is_add_app(e));
//    ios().get_diagnostic_channel() << "FUSE: " << e << "\n\n";
    flet<bool> no_recursive_fusion(m_fuse, false);

    /* Note: we assume all negations are on the outside of the summands */

    /* Example
       1. Input (e): n1 * x1 * n2 * x2 + x3 + - (x1 * x2 * n3) + (- x3) + x4
       2. Split summands: (n1 * n2) * (x1 * x2) + 1 * x3 + (- n3) * (x1 * x2) + (- 1) * x3 + 1 * x4
       3. Group by variable (e_grp): ((n1 * n2) * (x1 * x2) + (- n3) * (x1 * x2)) + (1 * x3 + (-1) * x3) + x4
       4. Introduce locals (e_grp_ls): ((n1 * n2) * l1 + (- n3) * l1) + (1 * l2 + (-1) * l2) + l3
       5. Fuse (e_fused_ls): (n1 * n2 + (- n3)) * l1 + (1 + (- 1)) * l2 + 1 * l3
       6. Simplify coefficients (e_simp_ls): (n1 * n2 + (- n3)) * l1 + l3
       7. Instantiate locals (e_simp): (n1 * n2 + (- n3)) * (x1 * x2) + x4

       Proofs
       1. Prove (1) == (3) using simplify with [ac]
       2. Prove (4) == (5) using simplify with [som]
       3. Prove (5) == (6) using simplify with [numeral]
       4. Prove (4) == (6) by transitivity of proofs (2) and (3)
       5. Prove (3) == (7) by instantiating proof (4)
       6. Prove (1) == (7) by transitivity of proofs (1) and (5)
    */

    /* Construct useful expressions */
    buffer<expr> args;
    get_app_args(e, args);
    expr T = args[0];
    expr f_add, f_mul, zero, one;
    try {
        f_add = get_app_builder().mk_partial_add(T);
        f_mul = get_app_builder().mk_partial_mul(T);
        zero = get_app_builder().mk_zero(T);
        one = get_app_builder().mk_one(T);
        expr left_distrib = get_app_builder().mk_partial_left_distrib(T);
    } catch (app_builder_exception & ex) {
        lean_trace(name({"simplifier", "failure"}),
                   tout() << "cannot synthesize necessary instances\n";);
        return result(e);
    }

    /* (1 ==> 2) Split each summand into (a) numerals and (b) variables */
    buffer<expr> numerals;
    buffer<expr> variables;
    expr s = e;
    while (is_add_app(s)) {
        buffer<expr> args;
        expr f = get_app_args(s, args);
        auto n_v = split_summand(args[2], f_mul, one);
        numerals.push_back(n_v.first);
        variables.push_back(n_v.second);
        s = args[3];
    }
    auto n_v = split_summand(s, f_mul, one);
    numerals.push_back(n_v.first);
    variables.push_back(n_v.second);
    lean_assert(numerals.size() == variables.size());

    /* (2 ==> 3, 4, 5) Group the summands by variable */
    expr_bi_struct_map<list<expr> > variable_to_numerals;
    for (unsigned i = 0; i < numerals.size(); i++) {
        auto it = variable_to_numerals.find(variables[i]);
        if (it != variable_to_numerals.end()) it->second = cons(numerals[i], it->second);
        else variable_to_numerals.insert({variables[i], list<expr>(numerals[i])});
    }

    expr e_grp = zero;
    expr e_grp_ls = zero;
    expr e_fused_ls = zero;

    buffer<expr> locals;
    variables.clear();
    for (auto v_ns : variable_to_numerals) {
        expr local;
        if (!is_one(v_ns.first)) {
            local = m_tmp_tctx->mk_tmp_local(T);
            locals.push_back(local);
            variables.push_back(v_ns.first);
        } else {
            local = v_ns.first;
        }

        expr term = zero;
        expr term_ls = zero;
        expr term_fused_ls = zero;
        for_each(v_ns.second, [&](expr const & n) {
                term = mk_app(f_add, mk_app(f_mul, v_ns.first, n), term);
                term_ls = mk_app(f_add, mk_app(f_mul, local, n), term_ls);
                term_fused_ls = mk_app(f_add, n, term_fused_ls);
            });
        e_grp = mk_app(f_add, term, e_grp);
        e_grp_ls = mk_app(f_add, term_ls, e_grp_ls);
        e_fused_ls = mk_app(f_add, mk_app(f_mul, term_fused_ls, local), e_fused_ls);
    }

    /* Prove (1) == (3) using simplify with [ac] */
    flet<bool> no_simplify_numerals(m_numerals, false);
    auto pf_1_3 = prove(get_app_builder().mk_eq(e, e_grp),
                        get_simp_lemmas(g_ac_key));

    if (!pf_1_3) {
        diagnostic(env(), ios()) << ppb(e) << "\n\n =?=\n\n" << ppb(e_grp) << "\n";
        throw blast_exception("Failed to prove (1) == (3) during fusion", e);
    }

    /* Prove (4) == (5) using simplify with [som] */
    auto pf_4_5 = prove(get_app_builder().mk_eq(e_grp_ls, e_fused_ls),
                        get_simp_lemmas(g_som_key));

    if (!pf_4_5) {
        diagnostic(env(), ios()) << ppb(e_grp_ls) << "\n\n =?=\n\n" << ppb(e_fused_ls) << "\n";
        throw blast_exception("Failed to prove (4) == (5) during fusion", e);
    }

    /* Prove (5) == (6) using simplify with [numeral] */
    flet<bool> simplify_numerals(m_numerals, true);
    result r_simp_ls = simplify(e_fused_ls, get_simp_lemmas(g_numeral_key));

    /* Prove (4) == (6) by transitivity of proofs (2) and (3) */
    expr pf_4_6;
    if (!r_simp_ls.has_proof()) pf_4_6 = *pf_4_5;
    else pf_4_6 = get_app_builder().mk_eq_trans(*pf_4_5, r_simp_ls.get_proof());

    /* Prove (3) == (7) by instantiating proof (4) */
    expr pf_3_7 = mk_app(Fun(locals, pf_4_6), variables);

    /* Prove (1) == (7) by transitivity of proofs (1) and (5) */
    expr pf_1_7 = get_app_builder().mk_eq_trans(*pf_1_3, pf_3_7);

    return result(mk_app(Fun(locals, r_simp_ls.get_new()), variables), pf_1_7);
}

expr_pair simplifier::split_summand(expr const & e, expr const & f_mul, expr const & one) {
    /* [e] is a possibly negated, possibly null product, where some of the multiplicands are numerals
       and the rest are treated as variables. This method does the following conversion:
       - (x1 * n1 * x2 * n3) ==> (-1 * n1 * n3) * (x1 * x2) */
    expr s = e;
    expr numeral = one;
    expr variable = one;
    if (is_neg_app(s)) {
        buffer<expr> args;
        get_app_args(s, args);
        numeral = get_app_builder().mk_app(get_neg_name(), one);
        s = args[2];
    }
    while (is_mul_app(s)) {
        buffer<expr> args;
        get_app_args(s, args);
        expr const & multiplicand = args[2];
        if (is_num(multiplicand)) {
            numeral = mk_app(f_mul, multiplicand, numeral);
        } else {
            if (variable == one) variable = multiplicand;
            else variable = mk_app(f_mul, multiplicand, variable);
        }
        s = args[3];
    }
    if (is_num(s)) {
        numeral = mk_app(f_mul, s, numeral);
    } else {
        if (variable == one) variable = s;
        else variable = mk_app(f_mul, s, variable);
    }
    return mk_pair(numeral, variable);
}

/* Setup and teardown */

void initialize_simplifier() {
    register_trace_class("simplifier");
    register_trace_class(name({"simplifier", "rewrite"}));
    register_trace_class(name({"simplifier", "congruence"}));
    register_trace_class(name({"simplifier", "failure"}));

    g_ac_key      = register_simp_lemmas({name{"simplifier", "prove"}, name{"simplifier", "unit"},
                                          name{"simplifier", "neg"}, name{"simplifier", "ac"}});
    g_som_key     = register_simp_lemmas({name{"simplifier", "prove"}, name{"simplifier", "unit"},
                                          name{"simplifier", "neg"}, name{"simplifier", "ac"}, name{"simplifier", "distrib"}});
    g_numeral_key = register_simp_lemmas({name{"simplifier", "unit"}, name{"simplifier", "neg"}, name{"simplifier", "ac"}});

    g_simplify_max_steps     = new name{"simplify", "max_steps"};
    g_simplify_top_down      = new name{"simplify", "top_down"};
    g_simplify_exhaustive    = new name{"simplify", "exhaustive"};
    g_simplify_memoize       = new name{"simplify", "memoize"};
    g_simplify_contextual    = new name{"simplify", "contextual"};
    g_simplify_expand_macros = new name{"simplify", "expand_macros"};
    g_simplify_fuse          = new name{"simplify", "fuse"};
    g_simplify_numerals      = new name{"simplify", "numerals"};

    register_unsigned_option(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS,
                             "(simplify) max allowed steps in simplification");
    register_bool_option(*g_simplify_top_down, LEAN_DEFAULT_SIMPLIFY_TOP_DOWN,
                         "(simplify) use top-down rewriting instead of bottom-up");
    register_bool_option(*g_simplify_exhaustive, LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE,
                         "(simplify) rewrite exhaustively");
    register_bool_option(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE,
                         "(simplify) memoize simplifications");
    register_bool_option(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL,
                         "(simplify) use contextual simplification");
    register_bool_option(*g_simplify_expand_macros, LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS,
                         "(simplify) expand macros");
    register_bool_option(*g_simplify_fuse, LEAN_DEFAULT_SIMPLIFY_FUSE,
                         "(simplify) fuse addition in distrib structures");
    register_bool_option(*g_simplify_numerals, LEAN_DEFAULT_SIMPLIFY_NUMERALS,
                         "(simplify) simplify (+, *, -, /) over numerals");
}

void finalize_simplifier() {
    delete g_simplify_numerals;
    delete g_simplify_fuse;
    delete g_simplify_expand_macros;
    delete g_simplify_contextual;
    delete g_simplify_memoize;
    delete g_simplify_exhaustive;
    delete g_simplify_top_down;
    delete g_simplify_max_steps;
}

/* Entry points */
static bool simplify_all_pred(expr const &) { return true; }

result simplify(name const & rel, expr const & e, simp_lemmas const & srss) {
    return simplifier(rel, simplify_all_pred)(e, srss);
}

result simplify(name const & rel, expr const & e, simp_lemmas const & srss, expr_predicate const & simp_pred) {
    return simplifier(rel, simp_pred)(e, srss);
}

}}
