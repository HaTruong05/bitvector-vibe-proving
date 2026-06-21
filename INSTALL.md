# Installation

Installation of packages necessary to check proofs of invertibility conditions in Coq.

## Requirements

- The library is designed to work on computers equipped with a POSIX (Unix or a clone) operating system. It is known to work under GNU/Linux (i386 and amd64) and Mac OS X.

- [Coq 8.20.0](https://github.com/coq/coq/tree/v8.20)

- [CoqHammer](https://github.com/lukaszcz/coqhammer)

## Installation of Packages using opam

### Install opam

We recommended to install the required packages from
[opam](https://opam.ocaml.org). Once you have installed opam on your system you
should issue the following command:

```bash
opam init
```

which will initialize the opam installation and prompt for modifying the shell
init file.

Once opam is installed you should still issue

```bash
eval $(opam env)
```

(this is not necessary if you start another session in your shell).

### Install OCaml

Now you can install an OCaml compiler (we recommend 4.14.1):

```bash
opam switch create <name> ocaml-base-compiler.4.14.1
eval $(opam env)
```

### Install Coq and CoqHammer

Add the Coq opam repository, then install Coq 8.20.0 and CoqHammer together in a single command. Installing them together ensures opam picks a version of CoqHammer compatible with Coq 8.20.0 and does not upgrade Coq to a newer incompatible version (Coq was rebranded as Rocq in version 9.x; the proofs require 8.20.0).

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.20.0 coq-hammer
```

If you also want to install CoqIDE:

```bash
opam install coqide.8.20.0
```

but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).

## Install BVList and IC Proofs

From the repository root, run:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

`BVList.v` is the bit-vector library; `InvCond.v` contains IC proofs over raw bit-vectors; `DepInvCond.v`
contains proofs of ICs over dependently-typed BVs.
