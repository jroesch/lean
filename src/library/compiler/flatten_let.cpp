/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/vm/vm.h"
#include "util/sstream.h"
#include "util/fresh_name.h"

namespace lean {
class flatten_let_fn : public compiler_step_visitor {
    buffer<buffer<pair<name, expr>>> m_bindings_stack;

    // Take a sequence of let bindings, splitting them into a linear sequence
    // of bindings, and returning the body expression.
    // virtual expr lift_let(expr const & _e) {
    //     expr e = _e;
    //     auto top = m_bindings_stack.back();
    //
    //     buffer<expr> locals;
    //
    //     while (is_let(e)) {
    //         auto n = let_name(e);
    //         locals.push_back(mk_local(n, mk_neutral_expr()));
    //         auto v = visit(let_value(e));
    //         e = visit(instantiate_rev(let_body(e), locals.size(), locals.data()));
    //         top.push_back(pair<name, expr>(n, v));
    //     }
    //
    //     return e;
    // }

    virtual expr visit_let(expr const & e) {
        auto ln = let_name(e);
        auto lv = visit(let_value(e));

        buffer<pair<name, expr>> & top = m_bindings_stack.back();

        top.push_back(pair<name, expr>(ln, lv));

        auto lb = visit(instantiate(let_body(e), mk_local(ln, mk_neutral_expr())));

        std::cout << "let_name: " << ln << std::endl;
        std::cout << "let_value: " << lv << std::endl;
        std::cout << "let_body: " << lb << std::endl;

        return lb;
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);

        if (is_internal_cases(fn) || is_constant(fn, get_nat_cases_on_name())) {
            buffer<expr> lifted_args;
            lifted_args.push_back(visit(args[0]));

            for (unsigned i = 1; i < args.size(); i++) {
                lifted_args.push_back(args[i]);
            }

            return mk_app(fn, lifted_args);
        } else {
            return compiler_step_visitor::visit_app(e);
        }
    }

    // virtual expr visit_let(expr const & e) {
    //     auto lb = let_body(e);
    //
    //     while (is_let(lv)) {
    //         expr v = instantiate_rev(let_value(lv), lifted_lets.size(), lifted_lets.data());
    //         lifted_lets.push_let(let_name(lv), mk_neutral_expr(), v);
    //         lv = v;
    //     }
    //
    //     lifted_lets.push_let(ln, mk_neutral_expr(), lv);
    //
    //     return lifted_lets.mk_let(lb);
    // }

    expr collect_bindings(expr const & e_, buffer<expr> & locals) {
        expr e = e_;
        while (is_lambda(e)) {
            name n = mk_fresh_name();
            locals.push_back(mk_local(n, mk_neutral_expr()));
            e = binding_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        return visit(e);
    }
public:
    expr operator()(expr const & e) {
      // This is temporary hack, better way would be to annotate all
      // terminating cf branches.
        std::cout << "expression here" << e << std::endl;
        buffer<expr> locals;
        auto ret_e = collect_bindings(e, locals);

        std::cout << "visited expr" << e << std::endl;
        if (m_bindings_stack.size() == 0) {
          std::cout << "this is 0 case here";
          return Fun(locals, ret_e);
        } else {
          std::cout << "this is non-zero case here";
          lean_assert(m_bindings_stack.size() == 1);
          auto scope = m_bindings_stack.back();
          unsigned i = scope.size();
          std::cout << "scope" << i << std::endl;
          while (i != 0) {
            std::cout << "intermediate" << ret_e << std::endl;
            auto binding = scope[i - 1];
            auto body = abstract(ret_e, mk_local(binding.first, mk_neutral_expr()));
            ret_e = mk_let(binding.first, mk_neutral_expr(), binding.second, body);
            i--;
          }
          std::cout << "final expr" << ret_e << std::endl;
          return Fun(locals, ret_e);
        }
    }

    flatten_let_fn(environment const & env):
    compiler_step_visitor(env), m_bindings_stack(buffer<buffer<pair<name, expr>>>()) {
      m_bindings_stack.push_back(buffer<pair<name, expr>>());
    }
};

expr flatten_let(environment const & env, expr const & e) {
    return flatten_let_fn(env)(e);
}
}
