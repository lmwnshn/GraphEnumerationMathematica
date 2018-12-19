# GraphEnumerationMathematica

This is a direct port of Doron Zeilberger's [GraphEnumeration](http://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/GE.html) package from Maple to Mathematica. It was ported as part of a class project for [15-354](https://www.cs.cmu.edu/~sutner/CDM/index.html), Computational Discrete Math.

The GraphEnumeration package deals with questions such as the number of Boolean functions under permutation and negation, the number of unlabeled connected graphs and trees, generating functions for those, and so on. The package implements Polya-Redfield counting. A better description can be found in the original package and/or Graphical Enumeration text by Frank Harary and Edgar Palmer. You can also find related OEIS numbers [here](https://oeis.org/HPGE.html).

The functions have the same names and calling conventions, modulo translation of language-specific nitpicking like list representation. Check out the usage strings and sample usage in the file.

## Known Issues and Workarounds

- Functionality
	- UGdeg and UMGdeg are too slow to run.
- Performance
	- I can't find anything in Mathematica that gives me the performance of subs() in Maple.
	- You can boost performance **significantly** by using dynamic scoping (Block[]) instead of lexical scoping (Module[]), but be very careful about your variable names when you do this. Don't pass in a Symbol that has the same name as a local variable in one of the dynamically scoped functions, otherwise you're in for a wild wonky ride.