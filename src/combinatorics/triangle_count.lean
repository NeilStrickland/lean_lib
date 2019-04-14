/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

(This is part of an attempt to formalise some material from
 a basic undergraduate combinatorics course.)

 Consider the set (T n) of triples (x,y,z) in ℕ³ with x + y + z = n.
 This can be drawn in an evident way as a triangle with sides of
 length n.  Inside (T n) there are many embedded copies of (T m) 
 for m = 1,..,n, which we call "embedded subtriangles".  The 
 total number of embedded subtriangles is (choose (n + 2) 3).  
 This can be proved in several different ways. 
-/