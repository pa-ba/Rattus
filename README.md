# Introduction

This library implements the Rattus programming language as an embedded
DSL. To this end the library provides a GHC plugin that performs the
additional checks that are necessary for Rattus.
            
Rattus is a functional reactive programming (FRP) language that uses
modal types to ensure operational properties that are crucial for
reactive programs: productivity (in each computation step, the program
makes progress), causality (output depends only on current and earlier
input), and no implicit space leaks (programs do not implicitly retain
memory over time).

A detailed introduction to the language with examples can be found in
this [paper](docs/paper.pdf), sections 2 and 3.
