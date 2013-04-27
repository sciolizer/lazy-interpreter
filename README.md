Writing an interpreter for a lazy functional language can be tricky.
The hard part is figuring out how to prevent shared sub-expressions
from being evaluated multiple times, without evaluating them
pre-maturely.

This project demonstrates a trick that can be used in haskell. Clever
use of unsafeInterleaveIO allows you to "lift" haskell's own lazy
evaluator into an interpreter.
