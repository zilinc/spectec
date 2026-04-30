(*

In this pass we remove pattern-matchings from two variables.

Imagine two datatypes A = Aone | Atwo | … | Aonehundred and B = Bone | Btwo | … | Bonehundred 

We would replace the following function:

f : A -> B -> C 
f Aone Bone = Cwhatever
f Atwo Btwo = Csomething

(which in proof assistants like Isabelle would explode in size as isabelle adds cases like f Aone Btwo = undefined etc for all ten thousand combinations) with three functions

fAone : B -> C
f Bone = Cwhatever

fAtwo : B -> C
f Btwo = Csomething

f : A -> B -> C
f Aone x = fAone x
f Atwo x = fAtwo x

Here, Isabelle would add 99 cases to fAone, 99 cases to fAtwo and 98 cases to f, instead of the 9998 cases it would otherwise have added to the old f

 *)


open Il.Ast
open Util.Source
open Xl.Mixop


let transform script =
  List.flatten (List.map transform_def script)
