{-
  `Grading` AND DIRECT CATEGORIES.

  Read in this order:

    Divisibility   the divisibility preorder of a promodel, and the
                   theorem that a `Grading` makes it a direct category in
                   ccl's sense (`Cubical.Categories.Direct.Base`)
    Proper         is `Proper` the non-identity maps?  (No: strictly more
                   general, and the maximal choice is not always
                   available)
    Later          is our `▷` the direct-category `▷`?  (Same
                   presentation; different category)
    Associativity  what `Fibered`'s missing associativity actually costs
    Group          `Instances/Group/NoGrading` re-read as a statement
                   about the divisibility category
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Everything where

import TheoryGrammar.Direct.Divisibility
import TheoryGrammar.Direct.Proper
import TheoryGrammar.Direct.Later
import TheoryGrammar.Direct.Associativity
import TheoryGrammar.Direct.Group
