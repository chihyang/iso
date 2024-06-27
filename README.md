# iso

This is the implementation of "[From Symmetric Pattern-Matching to Quantum
Control](https://arxiv.org/abs/1804.00952)".

## Build

``` shell
stack build
```

## Command

There are two modes: REPL mode or subcommand mode.  The former is the default
command.  When `iso-exe` is started without any argument, a REPL will start.
This can also be started by `iso-exe repl`.  All the other subcommands read from
an ISO program file and generate the required output.  The REPL also supports
all the other subcommands that `iso-exe` itself supports.  For example, `iso-exe
type <file>` returns the type of the given file.  In the REPL, this can also be
performed by using the prefix command `:lt <file>`.

In the REPL, you can use `:help` to see all the supported commands.

Outside the REPL, you can check all the available subcommands by using the
following command:

``` shell
/path/to/iso-exe --help
```

## Related Projects

* Theseus: https://github.com/chessai/theseus
* PERPL: https://github.com/diprism/perpl
* FGGS: https://github.com/diprism/fggs
