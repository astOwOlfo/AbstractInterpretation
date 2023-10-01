This is an unfinished [abstract interpreter](https://en.wikipedia.org/wiki/Abstract_interpretation) for a toy imperative language.
The finished parts are:
- A representation of the control flow graph is **implemented** and its semantics are **defined**.
- The iterator, i.e. the part that concerns itself with abstract interpretation of the control flow, is **implemented** and **certified**.

The unfinished parts are:
- The value domain, i.e. the part that concerns itself with abstract interpretation of arithmetic, is **not implemented**.
- There is no parser and no semantics defined for the toy language and nothing to translate it to the control flow graph format. For now, the project only concerns itself with the control flow graph.

The code quality of many proof scripts is low.
