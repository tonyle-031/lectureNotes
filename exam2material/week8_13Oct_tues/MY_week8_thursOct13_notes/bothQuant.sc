// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ¬(∃ x P(x)) |- ∀ x ¬P(x)

@pure def bothQuant[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 ( !(∃((x: T) => P(x))) ) by Premise,
      // build a AllI 
      2 Let((a: T) => SubProof (
        // use NegI to construct !P(a)
        3 SubProof (
          4 Assume ( P(a) ),
          // need: ∃((x: T) => P(x)) to contradict with premise
          5 ( ∃((x: T) => P(x)) ) by ExistsI[T](4),
          6 ( F ) by NegE(5, 1),
          // goal: contradiction (F)
        ),
        7 ( !P(a) ) by NegI(3),
        // goal: !P(a)
      )),
      8 ( ∀((x: T) => !P(x)) ) by AllI[T](2)
      // goal: ∀((x: T) => !P(x))
    )
  )
}