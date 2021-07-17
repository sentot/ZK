The ZK theorem proving system.

Copyright (c) 2021, Sentot Kromodimoeljo, William Pase, Mark Saaltink,
Dan Craigen and Irwin Meisels.

The ZK theorem proving system is a reimplementation of the theorem prover
component of the EVES verification system. It does away with the
imperative programming feature of EVES. The notation of ZK is a subset
of Verdi - the notation for EVES. Executable features of Verdi are not
supported but all non-executable features are supported.

Other differences from EVES/Verdi include the use of 16 inference rules
instead of 139, improved heuristics for recursive functions, and a
different syntax for hexadecimal numbers (prefixed with #x or #X
instead of #h or #H).

A notable feature of ZK is the ability to generate checkable proof
logs in terms of the 16 inference rules.

ZK is distributed under a BSD-type license (see license.pdf in the
doc subdirectory). As such, it would be a good candidate for a
back-end for an open-source version of Z/EVES.

An installation guide is provided (see installation.pdf in the doc
subdirectory). Some pre-built executables are provided in the bin
subdirectory.
