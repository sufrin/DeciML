# DeciML

A continuation-based interpreter for a language resembling ML.

Written in the early mid 2020s it was intended to demonstrate methods of
implementing call by name, and laziness alongside "normal"
call-by-value; and to explore the potential for escaping the "ascii"
straightjacket by using a much wider range of unicode glyphs in a
modern language.

It provides a complete example of the use of **sedlex** to construct
scanners that can usefully be used in an interactive setting.

The original intention was also to implement coroutines, but this
proved somewhat harder than I expected in its full generality on
account of some (well-judged) design decisions made in the
implementation of OCAML, and my distaste for the bounded-continuations
hack (sorry, *technique*).

**Bernard Sufrin, Oxford, mid-Covid-lockdown**
