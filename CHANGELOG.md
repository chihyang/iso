# Changelog for `iso`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Simple Branch 2024/3/18

### Attempt to simplify the AST:
1. Combined `Value` `Pattern` and `Exp` along with `Term` under one datatype `Term`. The changes did not accout for type-checking at this point
2. An `Iso` is also a `Term` using `TmIso` constructor, this is convenient to
3. Syntactic correctness is checked by parser
4. Also included "Fold"
5. Annotation is only for a `Term` (using `TmAnn`)

### Included a parser
- Potential problems in the ambiguity between `IsoApp` vs `TmApp`, `IsoVar` vs `TmVar` -- need more examination on this

### Included a evaluater of terms
Much simpler than using the complex AST.
