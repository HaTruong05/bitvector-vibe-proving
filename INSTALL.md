# Installation
Installation of packages necessary to check proofs of invertibility conditions in Coq.

## Requirements
- The library is designed to work on computers equipped with a POSIX (Unix or a clone) operating system. It is known to work under GNU/Linux (i386 and amd64) and Mac OS X.

- [Coq 8.20.0](https://github.com/coq/coq/tree/v8.20)

- [Coqhammer](https://github.com/lukaszcz/coqhammer)

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
eval `opam config env`
```

(this is not necessary if you start another session in your shell).

You need to have OCaml version >= 4.11.1 and Coq version 8.20.0.

> **Warning**: The version of Coq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.11.1.

### Install OCaml

Now you can install an OCaml compiler (we recommend 4.11.1):

```bash
opam switch create frocos23 ocaml-base-compiler.4.11.1
```

### Install Coq

After OCaml is installed, you can install Coq-8.20.0 through opam.

```bash
opam install coq.8.20.0
```

If you also want to install CoqIDE at the same time you can do

```bash
opam install coq.8.20.0 coqide.8.20.0
```
but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).


### Install CoqHammer

You can install CoqHammer through opam:

```bash
opam install coqhammer
```


## Install BVList and IC Proofs
Within root, run
```bash
coq_makefile -f _CoqProject -o Makefile
make
```
`BVList.v` is the bit-vector library; `InvCond.v` contains IC proofs over raw bit-vectors; `DepInvCond.v`
contains proofs of ICs over dependently-typed BVs.
