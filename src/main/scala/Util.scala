package de.tu_dresden.inf.lat.repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLSubClassOfAxiom}

import scala.jdk.StreamConverters.*

object Util {

  def maximalElements[T](elements: Iterable[T], po: PartialOrdering[T]): Set[T] = {
    elements.foldLeft(Set.empty[T])((maximalElements, element) => {
      if (maximalElements.exists(po.lteq(element, _)))
        maximalElements
      else
        maximalElements.filterNot(po.lteq(_, element)) + element
    })
  }

  def minimalElements[T](elements: Iterable[T], po: PartialOrdering[T]): Set[T] = {
    maximalElements(elements, po.reverse)
  }

  implicit class ImplicitBoolean(b: Boolean) {

    def implies(c: Boolean): Boolean = !b || c

  }

  class OWLSubClassOfAxiomReasonerRequest(subClassOfAxiom: OWLSubClassOfAxiom) {

    def wrt(reasoner: ELSubsumptionReasoner): Boolean =
      reasoner entails subClassOfAxiom

  }

  implicit class ImplicitOWLClassExpression(classExpression: OWLClassExpression) {

    lazy val isAtom: Boolean =
      classExpression match
        case c @ Class(_)              => !(c equals OWLThing)
        case ObjectSomeValuesFrom(_,_) => true
        case _                         => false

    def topLevelConjuncts(): LazyList[OWLClassExpression] =
      classExpression.conjunctSet().toScala(LazyList).filter(_.isAtom)

    def isSubsumedBy(other: OWLClassExpression): OWLSubClassOfAxiomReasonerRequest =
      OWLSubClassOfAxiomReasonerRequest(classExpression SubClassOf other)

    def subsumes(other: OWLClassExpression): OWLSubClassOfAxiomReasonerRequest =
      OWLSubClassOfAxiomReasonerRequest(other SubClassOf classExpression)

    lazy val reduced: OWLClassExpression = {
      val reasoner =
        ELSubsumptionReasoner(Set.empty, classExpression.nestedClassExpressions().toScala(LazyList), true)
      val reduction =
        if (classExpression subsumes OWLThing wrt reasoner)
          OWLThing
        else
          minimalElements(
            classExpression.topLevelConjuncts().map {
              case ObjectSomeValuesFrom(property, filler) => property some filler.reduced
              case c @ Class(_)                           => c
            },
            reasoner
          ) reduceLeft { _ and _ }
      reasoner.dispose()
      reduction
    }

    lazy val toDLString: String =
      classExpression match
        case OWLThing =>
          "⊤"
        case Class(iri) =>
          iri.toString()
        case ObjectSomeValuesFrom(property @ ObjectProperty(iri), filler) =>
          "∃" + iri.toString() + "." + filler.toDLString
        case ObjectIntersectionOf(operands) =>
          if (operands.isEmpty)
            "⊤"
          else if (operands.size == 1)
            operands.head.toDLString
          else
            "(" + operands.head.toDLString + operands.tail.foldLeft("")((str,op) => str + "⊓" + op.toDLString) + ")"
        case _ =>
          throw new IllegalArgumentException("Only 𝓔𝓛 concepts are supported.")

  }

  implicit class ImplicitOWLSubClassOfAxiom(subClassOfAxiom: OWLSubClassOfAxiom) {

    def isEntailedBy(reasoner: ELSubsumptionReasoner): Boolean =
      reasoner entails subClassOfAxiom

    lazy val toDLString: String =
      subClassOfAxiom.getSubClass.toDLString + " ⊑ " + subClassOfAxiom.getSuperClass.toDLString

  }

}
