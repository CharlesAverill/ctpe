---
title : Prologue - CTPE
---

# [Coq Tactics in Plain English](/ctpe/prologue.html)

If you're like me, one of the biggest shortcomings of the Coq ecosystem is the fairly complicated [tactic reference documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html).
It is exhaustive (which is better than lacking), but I have a few specific issues with it:

1. Entries are too verbose. I usually don't _need_ an exhaustive explanation of what a tactic does.
3. BNF grammar is not that easy to read. This one might be more controversial, but I would rather have **examples** of syntax.
4. There are not enough examples of tactics being used, and the examples that do exist are too often not representative of what a beginner might see.

For these reasons, I've decided to compile a reference document of every tactic that I've ever used, addressing the problems above via the following solutions.

1. Entries will be written at an undergraduate level, assuming a basic understanding of the Coq system. Sometimes, this will require reading the pages for other tactics before the one you really want to know about, but I think that's a fair compromise. Explanations will focus on what configurations of goal states the tactic is useful or not useful for.
2. Entries will start general and become more specific as one reads on. This will ensure minimal maintenance is necessary as tactics change over time.
3. Entries will include syntax *examples* rather than BNF grammars.
4. Entries will contain multiple examples, including goal states before and after executing the tactics. Small MRE Coq scripts may be included.
5. As a fallback, links to other resources, at minimum the official documentation, will be included in each entry.

This guide doesn't aim to replace the reference documentation, it aims to be a stepping stone into the reference documentation that reduces the apprehension of those new to Coq.

There are many other guides to Coq tactics, you should check them out too if I don't have what you need:

- [Coq Tactics Cheatsheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html)
- [More Basic Tactics - Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html)
- [Detailed examples of tactics](http://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual012.html)
- [Coq Tricks for Beginners with Too Many Examples](https://le.qun.ch/en/blog/coq/)
- [Coq Cheatsheet](https://julesjacobs.com/notes/coq-cheatsheet/coq-cheatsheet.pdf)
- [Coq cheat sheet](https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf)

<hr>
