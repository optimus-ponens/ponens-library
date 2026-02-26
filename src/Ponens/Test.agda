{-
TODO: Change --with-K to --cubical-compatible
This is blocked on AnyWithK.Any→∈-unique
-}
{-# OPTIONS --with-K --safe #-}

module Ponens.Test where

-- Import all files in the project to force type check of all.
-- TODO: Change this after project build setup, which should type check everything.
-- To find all the files:
-- `find -name "*.agda" | grep -v Ponens/Test.agda | sed 's/\.\//import /g' | sed 's/\//./g' | sed 's/\.agda//g'`
import Ponens.Data.DifferenceList.Properties
import Ponens.Data.Fin.Properties
import Ponens.Data.FinSet
import Ponens.Data.FinSet.Base
import Ponens.Data.FinSet.Binary
import Ponens.Data.List.Membership.Setoid.Properties
import Ponens.Data.List.Relation.Unary.Linked.Properties
import Ponens.Data.List.Relation.Unary.StrictSorted
import Ponens.Data.Maybe.Membership.Setoid
import Ponens.Data.Maybe.Relation.Unary.Any.Properties
import Ponens.Data.Product.Properties
import Ponens.Data.Tree.AVL.Indexed
import Ponens.Data.Tree.AVL.Indexed.Properties
import Ponens.Data.Tree.AVL.Indexed.Properties.All
import Ponens.Data.Tree.AVL.Indexed.Properties.Any
import Ponens.Data.Tree.AVL.Indexed.Properties.AnyWithK
import Ponens.Data.Tree.AVL.Indexed.Properties.Cast
import Ponens.Data.Tree.AVL.Indexed.Properties.Delete
import Ponens.Data.Tree.AVL.Indexed.Properties.Gap
import Ponens.Data.Tree.AVL.Indexed.Properties.Index
import Ponens.Data.Tree.AVL.Indexed.Properties.Join
import Ponens.Data.Tree.AVL.Indexed.Properties.JoinPieces
import Ponens.Data.Tree.AVL.Indexed.Properties.Lookup
import Ponens.Data.Tree.AVL.Indexed.Properties.Range
import Ponens.Data.Tree.AVL.Indexed.Properties.ToList
import Ponens.Data.Tree.AVL.Indexed.Properties.HeadTail
import Ponens.Function
import Ponens.Function.Properties
import Ponens.Function.Related.TypeIsomorphisms
import Ponens.Relation.Binary.Align
import Ponens.Relation.Binary.Construct.Subst.Equality
import Ponens.Relation.Nullary.Properties
import Ponens.Relation.Unary.Properties
