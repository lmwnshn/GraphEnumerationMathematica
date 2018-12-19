(* ::Package:: *)

(*
	15-354 Final Project, Fall 2018
	Wan Shen Lim (wanshenl)
	
	All the code in this package is a direct port of Doron Zeilberger's work,
	a Maple package (GraphEnumeration) that is available at
	http://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/GE.html
	
	The main functions provided in this package are same as the Maple version:
	1.  BnSeq[n]        : first n terms of sequence of number of equivalence classes of Boolean functions under permutation of variables and negation
	2.  BnxSeq[n, x]    : as above, but with generating functions based on the number of true rows in the truth table
	3.  Cseq[n]         : first n terms of sequence enumerating unlabeled connected graphs
	4.  Cseqx[n, x]     : as above, but with generating functions based on the number of edges
	5.  HGseq[k, n]     : first n terms of enumerating sequence for unlabeled regular k-hypergraphs
	6.  HGseqx[k, n, x] : as above, but with generating functions according to "edges"
	7.  Gseq[n]         : first n terms in the enumerating sequence for unlabeled graphs
	8.  Gseqx[n]        : as above, but with generating functions according to edges
	9.  RTseq[n]        : first n terms in the enumerating sequence for unlabeled rooted trees per Cayley
	10. Tseq[n]         : first n terms in the enumerating sequence for unlabeled trees
	11. UGdeg[L]*       : number of all (connected or otherwise) unlabeled simple graphs with degree sequence L
	12. UMGdeg[L]*      : number of all (connected or otherwise) unlabeled multigraphs with degree sequence L

	* I suspect 11 and 12 are broken.
	A mix of Mathematica being slow and Maple being different,
	and I was unable to debug the issue in time for submission.

	Caveat emptor, this port was written by someone who did not know either Maple or Mathematica before they started.
	Porting notes are listed below. Issues are primarily performance.
	
	0. [Philosophy] Porting Guidelines
		Keep function and variable names the same, even if you think of a better one, so that people can compare against the source.
		If Mathematica trivializes a function, use the Mathematica version.
	
	1. [Feature] Unported functions:
		Cx was not ported because the original Cx would always throw an error.
	
	2. [Performance] Scoping:
		Module[] is lexical scoping and Block[] is dynamic scoping. For some infathomable reason, Block is _MUCH_ faster.
		If you MUST compute some result, try replacing all Modules with Blocks.
		This is not the default because you introduce unexpected alpha-conversion issues,
		e.g. where you get different results if your input symbol is x instead of y.
	
	3. [Performance] Turtle functions:
		UGdeg and UMGdeg are the worst offenders, even with Block[] they are much slower in Mathematica than in the Maple equivalent.
		I have not figured out a way to speed it up.
		Other functions aren't too bad.
		
	4. Tests
		There is a small test suite at the bottom of this file.
		By default, they have been scaled down to complete within 15 seconds per test.
		

	Translated suggested usage from code comments in original package.
	If you want to figure out how to call a function, look here.
	Otherwise, all the public functions have usage strings.

	ApplySiPer[{1,0,1},{2,3,1}, {1,0,0}]
	Bn[3]
	BnSeq[7]
	Bnx[7,x]
	BnxSeq[5,x]
	CICube[s,3]
	CIk[s,2,3]
	Cseqx[10,y]
	Cx[3,t,x]
	HGnx[5,2,x]
	HGseq[2,10]
	InPer[{1,3,2},2]
	InSiPer[{1,3,2},{1,0,1}]
	Gnx[5,x]
	Gseq[10]
	Gseqx[10,y]
	MGseqx[10,y]
	MonoToDeg[Subscript[x,1]^2 * Subscript[x,2]^3, x, 2]
	Nx[3,x]
	NxMG[3,x,t,4]
	ParToCyc[{3,0,0}]
	UGdeg[{3,3,3,3,3,3}]
	UMGdeg[{3,3,3,3,3,3}]
	Wtk[{1,1},2,s]
	WtSiPer[{1,1},{1,0,1},s]
*)

BeginPackage["GraphEnumeration`"]

RTac::usage = "RTac[n] returns the number of rooted unlabeled trees on n vertices";
RTx::usage = "RTx[n, x] returns the first n terms of the generating function for the number of rooted unlabeled trees";
RTseq::usage = "RTseq[n] returns the first n terms of the sequence for the number of rooted labeled trees";
Tseq::usage = "Tseq[n] returns the first n terms of the generating function for the number of unlabeled trees";
Pars::usage = "Pars[n] returns the integer partitions of n in frequency notation";
Wt::usage = "Wt[j, s] returns the weight of a partition j where each item is scaled by its corresponding s";
Wt0::usage = "Wt0[j] returns the weight of a partition j";
CI::usage = "CI[s, n] returns the cycle-index polynomial of S_n using s[1], ... , s[n]";
Wt2::usage = "Wt2[j, s] returns the weight of a partition j for counting graphs";
CI2::usage = "CI2[s, n] returns the cycle-index polynomial of S_n using s[1], ... , s[n]";
Gnx::usage = "Gnx[n, x] returns the generating function of all unlabeled graphs with n vertices according to the number of edges";
Gseq::usage = "Gseq[n] returns the first n terms of the sequence counting the number of unlabeled graphs according to the number of vertices";
Cseq::usage = "Cseq[n] returns the first n terms of the sequence for counting unlabeled connected graphs";
Gseqx::usage = "Gseqx[n, x] returns the first n terms of the sequence of generating functions in x for the number of unlabeled graphs on n vertices according to the number of edges";
Cseqx::usage = "Cseqx[n, x] returns the first n terms of the sequence for counting unlabeled connected graphs";
MGnx::usage = "MGnx[n, x] returns the generating function of all unlabeled multi-edge graphs with n vertices according to the number of edges";
MGseqx::usage = "MGseqx[n, x] returns the first n terms of the sequence of generating functions in x for the number of unlabeled multi-graphs on n vertices according to edges";
MCseqx::usage = "MCseqx[n, m, y] returns the first n terms of the sequence for counting unlabeled connected multi-graphs with at most m edges";
ParToCyc::failure = "p[i] * i must be equal to the length of p";
ParToCyc::usage = "ParToCyc[p] returns the lex-smallest permutation of n with that cycle structure";
theta1::usage = "theta1[mono, n, x] applies the sorting operator theta on a monomial in x[1] ... x[n]";
theta::usage = "theta was not ported completely, missing type(-) functionality. It applies the sorting operator theta on a monomial in x[1] ... x[n]";
Wt2x::usage = "Wt2x[j, x] returns the weight according to the degrees of a partition j for counting graphs";
Nx::usage = "Nx[p, x] returns the enumerated weights of simple graphs on p vertices, x[1]^deg[1] * x[2]^deg[2] ...";
MonoToDeg::usage = "MonoToDeg[mono, x, n] returns the degree sequence of the monomial";
Cx::failure = "The original Cx code always errors out";
Cx::usage = "Cx[p, t, x] was not ported";
Wt2xMG::usage = "Wt2xMG[j, x, t, m] returns the weight according to degrees of up to 2M edges of a partition j for counting multi-graphs";
NxMG::usage = "NxMG[p, x, t, M] returns the enumerated weights of multigraphs on p vertices, x[1]^deg[1] * x[2]^deg[2] * ... * t^edges";
UMGdeg::usage = "\[AliasDelimiter][L] returns the number of all (connected or otherwise) unlabeled multigraphs with degree sequence L";
UGdeg::usage = "UGdeg[L] returns the number of all (connected ot otherwise) unlabeled simple graphs with degree sequence L";
NIVecs1::usage = "NIVecs1[k, a, N] returns the set of weakly decreasing vectors of non-negative integers of length k that start with a and add up to N";
NIPVecs::usage = "NIPVecs[k, N, a] returns the set of weakly decreasing vectors of positive integers <= a of length k that add up to N";
GrabCycle::usage = "GrabCycle[pi, i] returns the cycle belonging to i";
PerToCyc::usage = "PerToCyc[pi] returns the permutation as a cycle structure";
CycToPer::usage = "CycToPer[sig] returns the one-line permutation of the cycle";
Wtk::usage = "Wtk[j, k, s] returns the weight of partition j for counting k-uniform hypergraphs";
CIk::usage = "CIk[s, k, n] returns the cycle-index polynomial of S_n using s[1] ... s[n] for k-uniform hypergraphs";
HGnx::usage = "HGnx[n, k, x] returns the generating function of all unlabeled k-uniform hypergraphs with n vertices according to the number of edges";
HGn::usage = "HGn[n, k] returns the number of all unlabeled k-uniform hypergraphs with n vertices acccording to the number of edges";
HGseq::usage = "HGseq[k, n] returns the first n terms of the seqeuence counting the number of unlabeled k-uniformed hypergraphs";
HGseqx::usage = "HGseqx[k, n, x] returns the first n terms of the sequence counting the number of unlabeled k-uniform hypergraphs";
InPer::usage = "InPer[pi, k] returns the induced permutation on k-subsets of {1 ... n}";
ApplySiPer::usage = "ApplySiPer[v, pi, s] returns the vector v after applying signed permutation [pi, s]";
InSiPer::usage = "InSiPer[pi, s] returns the induced permutation on {0,1}^(|pi|)";
WtSiPer::failure = "Bad input, need |si| = n";
WtSiPer::usage = "WtSiPer[j, si, s] returns the weight of partition j and a sign vector for counting Boolean functions";
CICube::usage = "CICube[s, n] returns the cycle-index polynomial of the group of signed permutations acting on the Boolean lattice using s[1] ... s[n]";
Bn::usage = "Bn[n] returns the number of Boolean functions on n variables up to symmetry and negation";
Bnx::usage = "Bnx[n, x] returns the number of Boolean functions on n variables up to symmetry and negation";
BnSeq::usage = "BnSeq[n] returns the first n terms of the sequence for the number of Boolean functions on n variables up to symmmetry and negation";
BnxSeq::usage = "BnxSeq[n, x] returns the first n terms of the sequence for the number of Boolean functions on n variables up to symmetry and negation";


Begin["`Private`"]
RTac[n_] := RTac[n] = Module[
	{x, gu, i},
	If[n == 1, 1,
		gu = x / (Times @@ Table[(1-x^i)^RTac[i], {i, 1, n-1}]);
		gu = Series[gu, {x, 0, n}];
		SeriesCoefficient[gu, {x, 0, n}]
	]
]

(* OneStep is a helper function for RTx *)
OneStep[f_, x_] := Module[
	{gu, k, n},
	n = Exponent[f, x];
	gu = x * Exp[Plus @@ Table[ReplaceAll[x -> x^k][f] / k, {k, 1, n}]];
	gu = Series[gu, {x, 0, n+1}];
	Normal[gu]
]

RTx[n_, x_] := RTx[n, x] = Module[
	{gu, k},
	gu = x;
	Do[gu = Simplify[OneStep[gu, x]], n];
	gu
]

RTseq[n_] := RTseq[n] = Module[
	{x, gu, i},
	gu = RTx[n, x];
	Table[SeriesCoefficient[gu, {x, 0, i}], {i, 1, n}]
]

Tseq[n_] := Tseq[n] = Module[
	{gu, k, x},
	gu = RTx[n, x];
	gu = Expand[gu - (gu^2 - ReplaceAll[gu, x -> x^2])/2];
	Table[SeriesCoefficient[gu, {x, 0, k}], {k, 1, n}]
]

(* Not ported: Pars1 is unnecessary - this is faster *)

Pars[n_] := Pars[n] = Fold[
	Union[#1, {Table[Count[#2, i], {i, 1, n}]}]&, 
	{},
	IntegerPartitions[n]
]

Wt[j_, s_] := Wt[j, s] = Module[
	{k},
	Times @@ Table[
		(s[[k]]/k)^j[[k]]/Factorial[j[[k]]],
		{k, 1, Length[j]}
	]
]

Wt0[j_] := Wt0[j] = Module[
	{k},
	Wt[j, Table[1, {k, 1, Length[j]}]]
]

CI[s_, n_] := CI[s, n] = Module[
	{gu},
	gu = Pars[n];
	Plus @@ Table[Wt[gu[[i]], s], {i, 1, Length[gu]}]
]

Wt2[j_, s_] := Wt2[j, s] = Module[
	{n, k, gu, r, t},
	n = Length[j];
	(* weight *)
	gu = Wt0[j];
	(* both in same odd cycle (cl^2, odd) *)
	gu = gu * (Times @@ Table[Subscript[s,2*k+1]^(k*j[[2*k+1]]), {k, 1, IntegerPart[(n-1)/2]}]);
	(* both in same even cycle (cl^2, even) *)
	gu = gu * (Times @@ Table[(Subscript[s,k]*Subscript[s,2*k]^(k-1))^(j[[2*k]]), {k, 1, IntegerPart[n/2]}]);
	(* in different cycles of the same length ({c1,c2}, len(c1)=len(c2)) *)
	gu = gu * (Times @@ Table[Subscript[s,k]^(k*Binomial[j[[k]], 2]), {k, 1, n}]);
	(* in different cycles of different lengths ({c1,c2}, len(c1)<>len(c2)) *)
	gu = gu * (Times @@ Table[
					(Times @@ Table[Subscript[s,LCM[r,t]]^(GCD[r,t]*j[[r]]*j[[t]]), {r, 1, t-1}]),
					{t, 1, n}]);
	gu
]

CI2[s_, n_] := CI2[s, n] = Module[
	{gu, j},
	gu = Pars[n];
	Plus @@ Table[Wt2[gu[[j]], s], {j, 1, Length[gu]}]
]

Gnx[n_, x_] := Gnx[n, x] = Module[
	{gu, s, i, N},
	N = Max[Table[Table[LCM[r,t], {r, 1, t-1}], {t, 1, n}]];
	gu = CI2[s, n];
	Expand[ReplaceAll[Subscript[s,i_] -> 1+x^i][gu]]
]

(* Not ported: Gny is identical to Gnx *)

Gseq[n_] := Gseq[n] = Module[
	{i, x},
	Table[ReplaceAll[x -> 1][Gnx[i,x]], {i, 1, n}]
]

Cseq[n_] := Cseq[n] = Module[
	{gu, g, a, x, i, d, p},
	gu = Gseq[n];
	g = Log[1 + (Plus @@ Table[gu[[i]] * x^i, {i, 1, n}])];
	g = Series[g, {x, 0, n+1}];
	a = Table[SeriesCoefficient[g, {x, 0, i}], {i, 1, n}];
	Table[
		Plus @@ Table[MoebiusMu[d] / d * a[[p/d]], {d, Divisors[p]}],
		{p, 1, n}
	]
]

Gseqx[n_, y_] := Gseqx[n, y] = Module[
	{i},
	Table[Gnx[i, y], {i, 1, n}]
]

Cseqx[n_, y_] := Cseqx[n, y] = Module[
	{gu, g, a, i, r, p, q, tmoac, c, b},
	gu = Gseqx[n, y];
	tmoac = Symbol["tmoac"];
	g = Log[1 + (Plus @@ Table[gu[[i]] * tmoac^i, {i, 1, n}])];
	g = Series[g, {tmoac, 0, n+1}];
	a = Table[SeriesCoefficient[g, {tmoac, 0, i}], {i, 1, n}];
	b = Array[
			Function[{p, q}, SeriesCoefficient[a[[p]], {y, 0, q}]],
			{n, 1 + n^2},
			{1, 0}
		];
	c = Table[
			Table[
			(* port note: we add one because it was 0-indexed in maple *)
				Plus @@ Table[b[[p/r, q/r + 1]] * MoebiusMu[r]/r, {r, Divisors[GCD[p, q]]}],
				{q, 1, Binomial[p, 2]}
			],
			{p, 1, n}
		];
	Join[{1}, Table[
		Plus @@ Table[
			c[[p, q]] * y^q,
			{q, p-1, Binomial[p, 2]}
		],
		{p, 2, n}
	]]
]

MGnx[n_, x_] := MGnx[n, x] = Module[
	{gu, s, i, N, r, t},
	N = Max[Table[Table[LCM[r,t], {r, 1, t-1}], {t, 1, n}]];
	gu = CI2[s, n];
	Together[ReplaceAll[Subscript[s, i_] -> 1 / (1-x^i)][gu]]
]

MGseqx[n_, x_] := MGseq[n, x] = Module[
	{i},
	Table[MGnx[i, x], {i, 1, n}]
]

MCseqx[n_, m_, y_] := MCseqx[n, m, y] = Module[
	{gu, g, a, i, r, p, q, tmoac, c, b, j},
	gu = MGseqx[n, y];
	g = Log[1 + (Plus @@ Table[gu[[i]] * tmoac^i, {i, 1, n}])];
	g = Series[g, {tmoac, 0, n+1}];
	a = Table[Normal[SeriesCoefficient[g, {tmoac, 0, i}]], {i, 1, n}];
	a = Table[Series[a[[i]], {y, 0, m+1}], {i, 1, n}];
	a = Table[
			Plus @@ Table[
				SeriesCoefficient[a[[i]], {y, 0, j}] * y^j,
				{j, 0, m}
			], {i, 1, n}
		];
	b = Array[
			Function[{p, q}, SeriesCoefficient[a[[p]], {y, 0, q}]],
			{n, m+1},
			{1, 0}
		];
	c = Array[
			Function[{p, q}, Plus @@ Table[b[[p/r, q/r + 1]] * MoebiusMu[r]/r, {r, Divisors[GCD[p,q]]}]],
			{n, m},
			{1, 1}
		];
	Join[{1}, Table[
		Plus @@ Table[
			c[[p, q]] * y^q,
			{q, 1, m}
		],
		{p, 2, n}
	]]
]

ParToCyc[p_] := ParToCyc[p] = Module[
	{n, c, j, r, gu, i, i1},
	n = Length[p];
	If[
		Plus @@ Table[p[[i]] * i, {i, 1, n}] != n, 
		Message[ParToCyc::failure]
	];
	c = 0;
	gu = {};
	For[i = 1, i <= n, i = i + 1,
		(
			j = p[[i]];
			For[r = 1, r <= j, r = r + 1; c = c + i,
				gu = Join[gu, {Table[c+i1, {i1, 1, i}]}]
			]
		)
	];
	gu
]

theta1[mono_, n_, x_] := theta1[mono, n, x] = Module[
	{d, i, coe},
	d = Table[Exponent[mono, Subscript[x,i]], {i, 1, n}];
	coe = Normal[mono / (Times @@ Table[Subscript[x,i]^d[[i]], {i, 1, n}])];
	d = Sort[d];
	d = Table[d[[n+1-i]], {i, 1, n}];
	coe * (Times @@ Table[Subscript[x,i]^d[[i]], {i, 1, n}])
]

theta[pol_, n_, x_] := theta[pol, n, x] = Module[
	{i},
	Switch[
		Head[pol],
		Plus, Plus @@ Table[theta1[pol[[i]], n, x], {i, 1, Length[pol]}],
		Integer, pol,
		_, theta1[pol, n, x]
	]
]

Wt2x[j_, x_] := Wt2x[j, x] = Module[
	{p, gu, r, s, i, n, r1, s1},
	n = Length[j];
	p = ParToCyc[j];
	gu = 1;
	For[r = 1, r <= Length[p], r = r + 1,
		For[s = r + 1, s <= Length[p], s = s + 1,
			r1 = Length[p[[r]]];
			s1 = Length[p[[s]]];
			gu = gu * (1 +
				(Times @@ Table[Subscript[x,i]^(s1/GCD[r1,s1]), {i, p[[r]]}])
				* (Times @@ Table[Subscript[x,i]^(r1/GCD[r1,s1]), {i, p[[s]]}])	
			)^GCD[r1, s1];
		]
	];
	For[r = 1, r <= Length[p], r = r + 1,
		If[
			Equal[Mod[Length[p[[r]]], 2], 0],
			gu = gu
				* (1 + (Times @@ Table[Subscript[x,i], {i, p[[r]]}]))
				* (1 + (Times @@ Table[Subscript[x,i]^2, {i, p[[r]]}]))
				^ ((Length[p[[r]]] - 2)/2),
			gu = gu
				* (1 + (Times @@ Table[Subscript[x,i]^2, {i, p[[r]]}]))
				^ ((Length[p[[r]]] - 1)/2)
		];
	];
	
	gu = Expand[gu];
	theta[gu, n, x]
]

Nx[p_, x_] := Nx[p, x] = Module[
	{mu, j},
	mu = Pars[p];
	Expand[Plus @@ Table[Wt0[j] * Wt2x[j, x], {j, mu}]]
]

MonoToDeg[mono_, x_, n_] := MonoToDeg[mono, x, n] = Module[
	{i},
	Table[Exponent[mono, Subscript[x,i]], {i, 1, n}]
]

(* Not ported: original Cx currently always errors out *)
Cx[p_, t_, x_] := Cx[p, t, x] = Module[
	{},
	Message[Cx::failure]
]

Wt2xMG[j_, x_, t_, M_] := Wt2xMG[j, x, t, M] = Module[
	{p, gu, r, s, i, n, r1, s1, t1},
	n = Length[j];
	p = ParToCyc[j];
	gu = 1;
	For[r = 1, r <= Length[p], r = r + 1,
		For[s = r + 1, s <= Length[p], s = s + 1,
			r1 = Length[p[[r]]];
			s1 = Length[p[[s]]];
			gu = gu * (1 -
				(Times @@ Table[Subscript[x, i]^(s1/GCD[r1,s1]), {i, p[[r]]}])
				* (Times @@ Table[Subscript[x, i]^(r1/GCD[r1,s1]), {i, p[[s]]}])	
			)^(-GCD[r1, s1]);
		]
	];
	
	For[r = 1, r <= Length[p], r = r + 1,
		If[
			Equal[Mod[Length[p[[r]]], 2], 0],
			gu = gu
				* (1 - (Times @@ Table[Subscript[x, i], {i, p[[r]]}]))
				^ (-1)
				* (1 - (Times @@ Table[Subscript[x, i]^2, {i, p[[r]]}]))
				^ (-(Length[p[[r]]] - 2)/2),
			gu = gu
				* (1 - (Times @@ Table[Subscript[x, i]^2, {i, p[[r]]}]))
				^ (-(Length[p[[r]]] - 1)/2)
		];
	];
	
	gu = Normal[gu];
	gu = ReplaceAll[Subscript[x,i_] -> t * Subscript[x, i]][gu];
	gu = Series[gu, {t, 0, 2*M+1}];
	gu = Plus @@ Table[SeriesCoefficient[gu, {t, 0, i1}] * t^i1, {i1, 0, 2*M}];
	Plus @@ Table[theta[SeriesCoefficient[gu, {t, 0, i1}], n, x]*t^i1, {i1, 0, 2*M}]
]

NxMG[p_, x_, t_, M_] := NxMG[p, x, t, M] = Module[
	{mu, j, lu},
	mu = Pars[p];
	lu = Expand[Plus @@ Table[Wt0[j] * Wt2xMG[j, x, t, M], {j, mu}]];
	ReplaceAll[t -> t^(1/2)][lu]
]

(* TODO: too slow to run *)
UMGdeg[L_] := UMGdeg[L] = Module[
	{p, gu, x, i, M, t},
	p = Length[L];
	M = (Plus @@ L) / 2;
	gu = NxMG[p, x, t, M];
	gu = ReplaceAll[t -> 1][gu];
	For[i = 1, i <= p, i = i + 1,
		gu = SeriesCoefficient[gu, {Subscript[x,i], 0, L[[i]]}]
	];
	gu
]

(* TODO: too slow to run *)
UGdeg[L_] := UGdeg[L] = Module[
	{p, gu, x, i, M, t},
	p = Length[L];
	M = (Plus @@ L) / 2;
	gu = Nx[p, x];
	gu = ReplaceAll[t -> 1][gu];
	For[i = 1, i <= p, i = i + 1,
		gu = SeriesCoefficient[gu, {Subscript[x,i], 0, L[[i]]}]
	]
	gu
]

NIVecs1[k_, a_, N_] := NIVecs1[k, a, N] = Module[
	{gu, gu1, a1, g1},
	Which[
		a > N, {},
		k <= 0, {},
		And[k == 1, N != a], {},
		And[k == 1, N == a], {a},
		True, 
			gu = {};
			For[a1 = 0, a1 <= a, a1 = a1 + 1,
				gu1 = NIVecs1[k-1, a1, N-a];
				gu = Union[gu, Table[{Flatten[{a, g1}]}, {g1, gu1}]]
			];
			gu
	]
]

NIVecs[k_, N_, a_] := NIVecs[k, N, a] = Module[
	{a1},
	Which[
		And[k == 0, N == 0], {},
		k == 0, {},
		True, Select[Table[Flatten[NIVecs1[k,a1,N]], {a1, 0, Min[a, N]}], UnsameQ[#, {}] &]
	]
]

NIPVecs[k_, N_, a_] := NIPVecs[k, N, a] = Module[
	{gu, g, i},
	gu = NIVecs[k, N-k, a];
	Table[Table[g[[i]]+1, {i,1, Length[g]}], {g, gu}]
]


GrabCycle[pi_, i_] := GrabCycle[pi, i] = Module[
	{j, gu},
	gu = {i};
	If[pi[[i]] == i, gu, 
		j = pi[[i]];
		While [j != i,
			gu = Union[gu, {j}];
			j = pi[[j]]
		];
		gu
	]
]

PerToCyc[pi_] := PerToCyc[pi] = Module[
	{mu, gu, i, gu1},
	mu = pi;
	gu = {};
	While[mu != {},
		i = mu[[1]];
		gu1 = GrabCycle[pi, i];
		mu = Complement[mu, gu1];
		gu = Union[gu, {gu1}]
	];
	gu
]

InPer[pi_, k_] := InPer[pi, k] = Module[
	{T, mu, n, mu1, f, g, i},
	n = Length[pi];
	mu = Subsets[Range[1,n],{k}];
	T = AssociationMap[
		Function[{x}, Sort[Table[pi[[mu1]], {mu1, x}]]],
		mu
		];
	f = Association[];
	g = Association[];
	For[i = 1, i <= Length[mu], i = i + 1,
		AssociateTo[f, i -> mu[[i]]];
		AssociateTo[g, mu[[i]] -> i]
	];
	Table[g[T[mu[[i]]]], {i, 1, Length[mu]}]
]

CycToPer[sig_] := CycToPer[sig] = Module[
	{T, i, j, n},
	n = Plus @@ Table[Length[sig[[i]]], {i, 1, Length[sig]}];
	T = Association[];
	For[i=1, i <= Length[sig], i = i + 1,
		For[j=1, j <= Length[sig[[i]]] - 1, j = j + 1,
			AssociateTo[T, sig[[i,j]] -> sig[[i, j+1]]]];
		AssociateTo[T, sig[[i, Length[sig[[i]]]]] -> sig[[i,1]]]
	];
	Table[T[i], {i, 1, n}]
]

Wtk[j_, k_, s_] := Wtk[j, k, s] = Module[
	{gu, k1,i1, i2, i3, co, sig, i, gadol},
	gu = Times @@ Table[(1/k1)^j[[k1]]/Factorial[j[[k1]]], {k1, 1, Length[j]}];
	sig = {};
	co = 0;
	For[i1 = 1, i1 <= Length[j], i1 = i1 + 1,
		For[i2 = 1, i2 <= j[[i1]], i2 = i2 + 1; co = co + i1,
			sig = Union[sig, {Table[i3, {i3, co+1, co+i1}]}]
		]
	];
	sig = CycToPer[sig];
	sig = InPer[sig, k];
	sig = PerToCyc[sig];
	gadol = Max[Table[Length[sig[[i]]], {i, 1, Length[sig]}]];
	{gu * (Times @@ Table[Subscript[s, Length[sig[[i]]]], {i, 1, Length[sig]}]), gadol}
]

CIk[s_, k_, n_] := CIk[s, k, n] = Module[
	{gu, j},
	gu = Pars[n];
	{
		Plus @@ Table[Wtk[j, k, s][[1]], {j, gu}],
		Max[Table[Wtk[j,k,s][[2]], {j, gu}]]
	}
]

HGnx[n_, k_, x_] := HGnx[n, k, x] = Module[
	{gu, s, i},
	gu = CIk[s, k, n];
	Expand[ReplaceAll[Subscript[s,i_] -> 1 + x^i][gu[[1]]]]
]

HGn[n_, k_] := HGn[n, k] = Module[
	{gu, s, i},
	gu = CIk[s, k, n];
	Expand[ReplaceAll[Subscript[s,i_] -> 2][gu[[1]]]]
]

HGseq[k_, n_] := HGseq[k, n] = Module[
	{i, x},
	Table[HGn[i, k], {i, 1, n}]
]

HGseqx[k_, n_, x_] := HGseq[k, n, x] = Module[
	{i},
	Table[HGnx[i, k, x], {i, 1, n}]
]

ApplySiPer[v_, pi_, s_] := ApplySiPer[v, pi, s] = Module[
	{i, v1, v2},
	v1 = Table[v[[pi[[i]]]], {i, 1, Length[pi]}];
	v2 = {};
	For[i = 1, i <= Length[s], i = i + 1,
		If[
			s[[i]] == 1,
			v2 = Append[v2, v1[[i]]],
			v2 = Append[v2, 1 - v1[[i]]],
		]
	];
	v2
]

Cube1[n_] := Cube1[n] = {Array[List, ConstantArray[2, n], 0, ## &]}

InSiPer[pi_, s_] := InSiPer[pi, s] = Module[
	{T, mu, n, f, g, i},
	n = Length[pi];
	mu = Cube1[n];
	T = Association[];
	For[i = 1, i <= Length[mu], i = i + 1,
		AssociateTo[T, mu[[i]] -> ApplySiPer[mu[[i]], pi, s]]
	];
	f = Association[];
	g = Association[];
	For[i = 1, i <= Length[mu], i = i + 1,
		AssociateTo[f, i -> mu[[i]]];
		AssociateTo[g, mu[[i]] -> i]
	];
	Table[g[T[mu[[i]]]], {i, 1, Length[mu]}]
]

WtSiPer[j_, si_, s_] := WtSiPer[j, si, s] = Module[
	{gu, k1, i1, i2, i3, co, sig, i, gadol, n},
	n = Plus @@ Table[i * j[[i]], {i, 1, Length[j]}];
	If [Length[si] != n,
		Message[WtSiPer::failure],
		gu = Times @@ Table[(1/k1)^j[[k1]]/Factorial[j[[k1]]], {k1, 1, Length[j]}];
		sig = {};
		co = 0;
		For[i1 = 1, i1 <= Length[j], i1 = i1 + 1,
			For[i2 = 1, i2 <= j[[i1]], i2 = i2 + 1; co = co+ i1,
				sig = Union[sig, {Table[i3, {i3, co+1, co+i1}]}]
			]
		];
		sig = CycToPer[sig];
		sig = InSiPer[sig, si];
		sig = PerToCyc[sig];
		gadol = Max[Table[Length[sig[[i]]], {i, 1, Length[sig]}]];
		{
			gu * (Times @@ Table[Subscript[s, Length[sig[[i]]]], {i, 1, Length[sig]}]),
			gadol
		}
	]
]

CICube[s_, n_] := CICube[s, n] = Module[
	{gu1, gu2, j, g2, tot, ma, i},
	gu1 = Pars[n];
	gu2 = Cube1[n];
	ma = 0;
	tot = 0;
	For[i = 1, i <= Length[gu2], i = i + 1,
		g2 = gu2[[i]];
		tot = tot + (Plus @@ Table[WtSiPer[j, g2, s][[1]], {j, gu1}]);
		ma = Max[{ma, Table[WtSiPer[j, g2, s][[2]], {j, gu1}]}]
	];
	{tot, ma}
]

Bn[n_] := Bn[n] = Module[
	{gu, s, i},
	gu = CICube[s, n];
	Expand[ReplaceAll[Subscript[s, i_] -> 2][gu[[1]]]] / 2^n
]

Bnx[n_, x_] := Bnx[n, x] = Module[
	{gu, s, i},
	gu = CICube[s, n];
	Expand[ReplaceAll[Subscript[s, i_] -> 1 + x^i][gu[[1]]]] / 2^n
]

BnSeq[n_] := BnSeq[n] = Module[
	{n1},
	Table[Bn[n1], {n1, 1, n}]
]

BnxSeq[n_, x_] := BnxSeq[n, x] = Module[
	{n1},
	Table[Bnx[n1, x], {n1, 1, n}]
]


End[]


(* ::InheritFromParent:: *)
(**)


(* ::InheritFromParent:: *)
(**)


EndPackage[]


(* ::InheritFromParent:: *)
(**)


(* Test cases. Numbers scaled down to finish in at most 15 seconds per test. *)


(* BnSeq[n] returns the first n terms of the sequence enumerating equivalence classes of Boolean functions under permutation of variables and negation *)
(* OEIS sequence: https://oeis.org/A000616 *)
(* Zeilberger test case 1: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration1 *)
TimeConstrained[BnSeq[7] // Timing, 15]


(* BnxSeq[n, x] returns the first n terms of the sequence of weight-enumerators of equivalence classes of Boolean functions under permutation of variables and negation *)
(* Zeilberger test case 2: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration2 *)
TimeConstrained[BnxSeq[7, x] // Timing, 15]


(* Cseq[n] returns the number of connected graphs with n nodes *)
(* OEIS sequence: https://oeis.org/A001349 *)
(* Zeilberger test case 3: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration3 *)
TimeConstrained[Cseq[20] // Timing, 15]


(* Gseq[n] returns the number of graphs on n unlabeled nodes *)
(* OEIS sequence: https://oeis.org/A001349 *)
(* Zeilberger test case 4: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration4 *)
TimeConstrained[Gseq[20] // Timing, 15]


(* ::InheritFromParent:: *)
(**)


(* Tseq[n] returns the number of trees with n unlabeled nodes *)
(* OEIS sequence: https://oeis.org/A000055 *)
(* Zeilberger test case 5: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration5 *)
TimeConstrained[Tseq[60] // Timing, 15]


(* HGseq[k, n] returns the first n terms of the sequence enumerating k-regular hypergraphs *)
(* OEIS sequence: https://oeis.org/A000665 *)
(* Zeilberger test case 6: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration6 *)
TimeConstrained[HGseq[3, 10] // Timing, 15]


(* UGdeg[L] returns the number of unlabeled simple graphs with |L| vertices for the given degree sequence *)
(* Zeilberger test case 7: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration7 *)
TimeConstrained[UGdeg[{3,3,3,3,3,3}] // Timing, 15]


(* UMGdeg[L] returns the number of unlabeled multi-graphs with |L| vertices for the given degree sequence *)
(* Zeilberger test case 8: http://sites.math.rutgers.edu/~zeilberg/tokhniot/inGraphEnumeration8 *)
TimeConstrained[UMGdeg[{3,3,3,3,3,3}] // Timing, 15]
