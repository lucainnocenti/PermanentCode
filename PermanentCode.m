(* ::Package:: *)

BeginPackage["PermanentCode`"];

(*If the symbol System`Permanent exists (it was introduced circa Mathematica 10.2.0) then System`Permanent is Unprotected[_],System`Permanent is Removed[_];and finally,a new function PermanentCode`Permanent[_] is defined.In general PermanentCode`Permanent[mArg] returns the same result as System`Permanent[mArg].However,numerical arguments having precision MachinePrecision are evaluated by compiled C-code;for large matrices this C-code is 1000X (or more) faster than System`Permanent.*)

If[(*this version of Mathematica defines System`Permanent[_]*)"System`Permanent"//NameQ,(*then remove System`Permanent[_] and issue a warning*)Permanent::removed="(caveat) the function `1`Permanent[_] has been removed; "<>"the new function `2`Permanent[_] compatibly replaces it "<>"(with faster evaluation).";
Message[Permanent::removed,Permanent//Context,$ContextPath//First];
If[Permanent//Attributes//MemberQ[#,Protected]&,Unprotect[Permanent];];
ClearAll["System`Permanent"];
Remove["System`Permanent"];];

(*ClearAll definitions in the present Context*)
ClearAll[Context[]<>"*"//Evaluate];

Permanent::usage="\<Permanent[mArg_List?MatrixQ] is computed by Glynn's formula.  The 
algorithm requires O(m^2 2^m) operations, where m is the dimension 
of the matrix arg.

Compiled evaluation is applied solely to arguments \"mArg\" that match 
either of following patterns:

     MatrixQ[mArg,IntegerQ]
     MatrixQ[mArg,MachineNumberQ]

NEAT EXAMPLES: Integer-to-Real conversions commonly evaluate more 
quickly than \"Permanent[mArg_?MatrixQ]\", per the following idiom:

     Permanent[mArg_?Integer] := Permanent[mArg//
         SetPrecision[#,MachinePrecision]&]//Round

POSSIBLE ISSUES: For Integer arguments, the compiled C-code uses 8-byte 
integers(apparently); hence too-large integer-valued permanents elicit 
an overflow (?) error as follows: 

  CompiledFunction::cfne: Numerical error encountered; 
   proceeding with uncompiled evaluation.

NOTES 
(1) Glynn's formula is re-ordered with a view to speed-by-simplicity 
    (at negligible cost in formal efficiency); in brief the algorithm
    is implemented as a sequence of BLAS-compatible calls to built-in 
    Mathematica (BLAS) functions.
(2) At present the algorithm does not fully exploit the Gray-code 
    structure of an (internal) permutation list.

RESOURCES
URL: http://en.wikipedia.org/wiki/Computing_the_permanent#Glynn_formula
URL: http://en.wikipedia.org/wiki/Basic_Linear_Algebra_Subprograms
URL: http://mathematica.stackexchange.com/q/38177\>";

directPermanent::usage="\<directPermanent[_] is computed (inefficiently) by a \"no-tricks\" combinatorical sum.\>";

Begin["`Private`"];
ClearAll[Context[]<>"*"//Evaluate];

directPermanent[\[DiamondSuit]mArg_List?SquareMatrixQ]:=Module[{\[DiamondSuit]rowList,\[DiamondSuit]colPerms},\[DiamondSuit]rowList=\[DiamondSuit]mArg//Length//Range;
\[DiamondSuit]colPerms=\[DiamondSuit]rowList//Permutations;
Map[(MapThread[\[DiamondSuit]mArg[[#1,#2]]&,{\[DiamondSuit]rowList,#}]//Times@@#&)&,\[DiamondSuit]colPerms]//Plus@@#&//(\[DiamondSuit]rowList=.;\[DiamondSuit]colPerms=.;#)&];

(*this is Permanent's sole DownValue,i.e,Permanent is defined solely as a wrap around \[DiamondSuit]Permanent*)
Permanent[\[DiamondSuit]mArg_?SquareMatrixQ]:=\[DiamondSuit]Permanent[\[DiamondSuit]mArg];

(*-------------------------------------------Remarks upon Precision and MachinePrecision-------------------------------------------The function Precision treats the symbol MachinePrecision in a special way:"If x is not a number, Precision[x] 
gives the minimum value of Precision for all the numbers 
that appear in x. MachinePrecision is considered smaller 
than any explicit precision." That is why {1.0,1.0//SetPrecision[#,0.5*MachinePrecision]&}//Precision//Print;
prints "MachinePrecision".It follows that patterns that match low-precision matrices have to examine the matrix elements individually (as below).*)

\[DiamondSuit]Permanent[(*low-precision evaluation wrapper*)\[DiamondSuit]mArg_?MatrixQ/;MemberQ[\[DiamondSuit]mArg,_?(Precision[#]<MachinePrecision&),{2}]]:=Module[{\[DiamondSuit]precision},\[DiamondSuit]precision=\[DiamondSuit]mArg//Precision;
\[DiamondSuit]mArg//SetPrecision[#,MachinePrecision]&//\[DiamondSuit]Permanent//SetPrecision[#,\[DiamondSuit]precision]&];

\[DiamondSuit]glynnSignList::usage="\<List of Gray-code permutations, saved in-memory 
for use by Permanent[_]'s Glynn-formula.\>";

\[DiamondSuit]glynnSignListMostRecentArgument=1;

(*ensure that the only DownValues stored for \[DiamondSuit]glynnSignList[\[DiamondSuit]mArg_Integer] are for \[DiamondSuit]mArg=1 and \[DiamondSuit]mArg=\[DiamondSuit]glynnSignListMostRecentArgument*)

\[DiamondSuit]glynnSignList[1]:=(If[\[DiamondSuit]glynnSignListMostRecentArgument>1,\[DiamondSuit]glynnSignList[\[DiamondSuit]glynnSignListMostRecentArgument]=.;
\[DiamondSuit]glynnSignListMostRecentArgument=1;];
{{1}});

\[DiamondSuit]glynnSignList[\[DiamondSuit]m_Integer]/;(\[DiamondSuit]m>1):=(\[DiamondSuit]glynnSignList[\[DiamondSuit]m]=\[DiamondSuit]glynnSignList[\[DiamondSuit]m-1]//((*to conserve memory,purge unneeded DownValues*)If[(\[DiamondSuit]m-1)>1,\[DiamondSuit]glynnSignList[\[DiamondSuit]m-1]=.;];
If[\[DiamondSuit]m<\[DiamondSuit]glynnSignListMostRecentArgument,\[DiamondSuit]glynnSignList[\[DiamondSuit]glynnSignListMostRecentArgument]=.;];
\[DiamondSuit]glynnSignListMostRecentArgument=\[DiamondSuit]m;
#)&//(Map[({1,1}~Join~(#//Rest))&,#]~Join~Map[({1,-1}~Join~(#//Rest))&,#//Reverse])&);

\[DiamondSuit]compiledGlynnProductInteger=Compile[{{\[DiamondSuit]d,_Integer,1},{\[DiamondSuit]a,_Integer,2}},Apply[Times,(\[DiamondSuit]d.\[DiamondSuit]a)],CompilationTarget->"C",RuntimeAttributes->{Listable},Parallelization->True
(*(*Caveat:enable for~2x speed,less robustness*)
,RuntimeOptions\[Rule]{CatchMachineIntegerOverflow\[Rule]False}*)];

\[DiamondSuit]compiledGlynnProductReal=Compile[{{\[DiamondSuit]d,_Integer,1},{\[DiamondSuit]a,_Real,2}},Apply[Times,(\[DiamondSuit]d.\[DiamondSuit]a)],CompilationTarget->"C",RuntimeAttributes->{Listable},Parallelization->True];

\[DiamondSuit]compiledGlynnProductComplex=Compile[{{\[DiamondSuit]d,_Integer,1},{\[DiamondSuit]a,_Complex,2}},Apply[Times,(\[DiamondSuit]d.\[DiamondSuit]a)],CompilationTarget->"C",RuntimeAttributes->{Listable},Parallelization->True];

(*----------------------------------------------Remarks upon "RuntimeAttributes -> {Listable}"---------------------------------------------- For compiled functions Mathematica applies RuntimeAttribute "Listable" attribute differently than for rule-based functions;
namely:"When the arguments [of a 'Listable' compiled function]
include a list with higher rank than the input specification, 
the function threads over that argument." See:Compile/tutorial/Operation#76381003 Thus we have f=Compile[{{a,_Integer,1},{b,_Integer,2}},{a,b//Flatten},CompilationTarget\[Rule]"C",RuntimeAttributes\[Rule]{Listable},Parallelization\[Rule]True];
f[{{1,2}},{{3,4}}]==={{{1,2},{3,4}}} whereas in contrast,a non-compiled version of the same Listable function threads over*all*arguments SetAttributes[g,Listable] g[a_,b_]:={a,b};
g[{{1,2}},{{3,4}}]==={{{1,3},{2,4}}} The following Permanent//DownValues relies crucially upon the just-described "RuntimeAttributes -> {Listable}" behavior of compiled functions.*)

\[DiamondSuit]Permanent[(*purely _Integer matrices*)\[DiamondSuit]mArg_?(MatrixQ[#,IntegerQ]&)]:=\[DiamondSuit]compiledGlynnProductInteger[\[DiamondSuit]glynnSignList[\[DiamondSuit]mArg//Length],\[DiamondSuit]mArg]//Total[#[[1;; ;;2]]]-Total[#[[2;; ;;2]]]&//#/2^((\[DiamondSuit]mArg//Length)-1)&;

\[DiamondSuit]Permanent[(*purely _Real MachineNumber matrices*)\[DiamondSuit]mArg_?((MatrixQ[#,MachineNumberQ]&&FreeQ[#,_Complex,{2}])&)]:=\[DiamondSuit]compiledGlynnProductReal[\[DiamondSuit]glynnSignList[\[DiamondSuit]mArg//Length],\[DiamondSuit]mArg]//Total[#[[1;; ;;2]]]-Total[#[[2;; ;;2]]]&//#/2^((\[DiamondSuit]mArg//Length)-1)&;

\[DiamondSuit]Permanent[(*by default,at least one _Complex MachineNumber*)\[DiamondSuit]mArg_?(MatrixQ[#,MachineNumberQ]&)]:=(*the following encompasses the general case of pure _Complex "MachineNumberQ" matrices,and also mixed _Real and _Complex "MachineNumberQ" matrices,by virtue of a "CoerceTensor" call in the compiled C-code*)\[DiamondSuit]compiledGlynnProductComplex[\[DiamondSuit]glynnSignList[\[DiamondSuit]mArg//Length],\[DiamondSuit]mArg]//Total[#[[1;; ;;2]]]-Total[#[[2;; ;;2]]]&//#/2^((\[DiamondSuit]mArg//Length)-1)&;

\[DiamondSuit]Permanent[(*the most general case;including symbolic extended-precision,and mixed-type matrices;thus including (for example) matrix arguments that match (MemberQ[#,_Integer,{2}]&&MemberQ[#,_Real,{2}])& and hence match no prior \[DiamondSuit]Permanent DownValue.*)\[DiamondSuit]mArg_?MatrixQ]:=Map[Apply[Times,#.\[DiamondSuit]mArg]&,\[DiamondSuit]glynnSignList[\[DiamondSuit]mArg//Length]]//Total[#[[1;; ;;2]]]-Total[#[[2;; ;;2]]]&//#/2^((\[DiamondSuit]mArg//Length)-1)&;

End[];
EndPackage[];
