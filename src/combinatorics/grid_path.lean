/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

(This is part of an attempt to formalise some material from
 a basic undergraduate combinatorics course.)

 An (n,m) - grid path is a path in {0,..,n} × {0,..,m} that
 starts at (0,0) and ends at (m,m), where each step moves
 one unit to the right or one unit upwards.

 The set of (n,m) - grid paths bijects naturally with the
 set of subsets of size n in {0,...,n+m-1} (by considering 
 which of the steps are horizontal).  There is an evident 
 bijection between (n,m) - grid paths and (m,n) - grid paths.
-/