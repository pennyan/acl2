; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-dynamic-semantics
  :parents (atc-implementation)
  :short "A dynamic semantics of C for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to support the generation of proofs for
     the C code generated by ATC,
     we need a dynamic (i.e. execution) semantics
     of (the needed portion of) C.
     The dynamic semantics serves to prove that
     the generated C code is functionally equivalent to
     the ACL2 code from which it is generated.
     Here we provide an initial formal dynamic semantics,
     which should support the generation of proofs
     for the initial version of ATC.")
   (xdoc::p
    "This model also provides a target for APT derivations.
     ATC recognizes some of the ACL2 functions in this model
     and translates them to the corresponding C constructs.")
   (xdoc::p
    "This preliminary dynamic semantics may be extended in the future,
     and may be replaced by a more comprehensive model
     that we will be developing as part of the "
    (xdoc::seetopic "language" "language formalization")
    ".")
   (xdoc::p
    "The dynamic semantics is defined over the C abstract syntax,
     but for now it does not support the execution of some constructs,
     just because currently ATC does not generate those constructs.
     This way, we keep the dynamic semantics simpler.
     Being more restrictive is adequate here:
     if we have a proof of functional equivalence between some ACL2 code
     and some C code according to this restriction dynamic semantics,
     it means that the C code only uses the constructs that we cover,
     which is a subset of valid C.")
   (xdoc::p
    "The current definition of this dynamic semantics
     may not be completely accurate in terms of
     execution of arbitrary C in the covered subset of C,
     in particular in the treatment of arrays.
     However, it is accurate for the C programs generated by ATC.
     This dynamic semantic is work in progress;
     we plan to make it completely accurate
     for all the covered subset of C."))
  :order-subtopics t
  :default-parent t)
