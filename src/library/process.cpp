/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <unistd.h>
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>

#define BUFSIZE 4096
#else
#include <sys/wait.h>
#endif
#include "library/process.h"
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean {

process::process(std::string n): m_proc_name(n), m_args() {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

process & process::set_stdin(stdio cfg) {
    m_stdin = optional<stdio>(cfg);
    return *this;
}

process & process::set_stdout(stdio cfg) {
    m_stdout = optional<stdio>(cfg);
    return *this;
}

process & process::set_stderr(stdio cfg) {
    m_stderr = optional<stdio>(cfg);
    return *this;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

HANDLE to_win_handle(FILE * file) {
    return _get_osfhandle(fileno(file));
}

FILE * from_win_handle(HANDLE handle, char const * mode) {
    return fd_open_open_osfhandle(reinterpret_cast<int_ptr_t>(handle));
}

void create_child_process(HANDLE hstdin, HANDLE hstdout, HANDLE hstderr);

// This code is adapted from: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682499(v=vs.85).aspx
child process::spawn() {
   SECURITY_ATTRIBUTES saAttr;
   HANDLE child_stdin_read = NULL;
   HANDLE child_stdin_write = NULL;
   HANDLE child_stdout_read = NULL;
   HANDLE child_stdout_write = NULL;

   // Set the bInheritHandle flag so pipe handles are inherited.
   saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
   saAttr.bInheritHandle = TRUE;
   saAttr.lpSecurityDescriptor = NULL;

   // Create a pipe for the child process's STDOUT.
   if ( ! CreatePipe(&child_stdout_read, &child_stdout_write, &saAttr, 0) )
      throw new exception("unable to construct stdout pipe");

   // Ensure the read handle to the pipe for STDOUT is not inherited.
   if ( ! SetHandleInformation(child_stdout_read, HANDLE_FLAG_INHERIT, 0) )
      throw new exception("unable to configure stdout pipe");

    // Create a pipe for the child process's STDIN.
   if (! CreatePipe(&child_stdin_read, &child_stdin_write, &saAttr, 0))
      throw new exception("unable to construct stdin pipe");

   // Ensure the write handle to the pipe for STDIN is not inherited.
   if ( ! SetHandleInformation(child_stdin_write, HANDLE_FLAG_INHERIT, 0) )
      throw new exception("unable to configure stdin pipe");

   // Create the child process.
   create_child_process(child_stdin_read, child_stdout_write, child_stdout_write);

   return child(0, 
        std::make_shared<handle>(from_win_handle(child_stdin_write)),
        std::make_shared<handle>(from_win_handle(child_stdout_read)),
        std::make_shared<handle>(from_win_handle(child_stdout_read))); 
}

void create_child_process(HANDLE hstdin, HANDLE hstdout, HANDLE hstderr)
// Create a child process that uses the previously created pipes for STDIN and STDOUT.
{
   TCHAR szCmdline[]=TEXT("child");
   PROCESS_INFORMATION piProcInfo;
   STARTUPINFO siStartInfo;
   BOOL bSuccess = FALSE;

// Set up members of the PROCESS_INFORMATION structure.

   ZeroMemory( &piProcInfo, sizeof(PROCESS_INFORMATION) );

// Set up members of the STARTUPINFO structure.
// This structure specifies the STDIN and STDOUT handles for redirection.

   ZeroMemory( &siStartInfo, sizeof(STARTUPINFO) );
   siStartInfo.cb = sizeof(STARTUPINFO);
   siStartInfo.hStdError = hstderr;
   siStartInfo.hStdOutput = hstdout;
   siStartInfo.hStdInput = hstdin;
   siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

// Create the child process.

   bSuccess = CreateProcess(NULL,
      szCmdline,     // command line
      NULL,          // process security attributes
      NULL,          // primary thread security attributes
      TRUE,          // handles are inherited
      0,             // creation flags
      NULL,          // use parent's environment
      NULL,          // use parent's current directory
      &siStartInfo,  // STARTUPINFO pointer
      &piProcInfo);  // receives PROCESS_INFORMATION

   // If an error occurs, exit the application.
   if (!bSuccess) {
       throw exception("failed to start child process");
   } else {
      // Close handles to the child process and its primary thread.
      // Some applications might keep these handles to monitor the status
      // of the child process, for example.

      CloseHandle(piProcInfo.hProcess);
      CloseHandle(piProcInfo.hThread);
   }
}

void process::run() {
     throw exception("process::run not supported on Windows");
}

#else

optional<pipe> setup_stdio(optional<stdio> cfg) {
    /* Setup stdio based on process configuration. */
    if (cfg) {
        switch (*cfg) {
        /* We should need to do nothing in this case */
        case stdio::INHERIT:
            return optional<pipe>();
        case stdio::PIPED: {
            return optional<pipe>(lean::pipe());
        }
        case stdio::NUL: {
            /* We should map /dev/null. */
            return optional<pipe>();
        }
        default:
           lean_unreachable();
        }
    } else {
        return optional<pipe>();
    }
}

child process::spawn() {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe = setup_stdio(m_stdin);
    auto stdout_pipe = setup_stdio(m_stdout);
    auto stderr_pipe = setup_stdio(m_stderr);

    int pid = fork();

    if (pid == 0) {
        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        }

        buffer<char*> pargs;

        for (auto arg : this->m_args) {
            auto str = new char[arg.size() + 1];
            arg.copy(str, arg.size());
            str[arg.size()] = '\0';
            pargs.push_back(str);
        }

        pargs.data()[pargs.size()] = NULL;

        auto err = execvp(pargs.data()[0], pargs.data());
        if (err < 0) {
            throw std::runtime_error("executing process failed: ...");
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    }

    /* We want to setup the parent's view of the file descriptors. */
    int parent_stdin = STDIN_FILENO;
    int parent_stdout = STDOUT_FILENO;
    int parent_stderr = STDERR_FILENO;

    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = stdin_pipe->m_write_fd;
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = stdout_pipe->m_read_fd;
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = stderr_pipe->m_read_fd;
    }

    return child(pid,
         std::make_shared<handle>(fdopen(parent_stdin, "w")),
         std::make_shared<handle>(fdopen(parent_stdout, "r")),
         std::make_shared<handle>(fdopen(parent_stderr, "r")));
}

void process::run() {
    child ch = spawn();
    int status;
    waitpid(ch.m_pid, &status, 0);
}

#endif

}
