package de.tu_dresden.inf.lat.repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.vocab.OWLRDFVocabulary

import scala.jdk.StreamConverters.*

/**
 * Used to check whether an ontology is fully supported, i.e., does not contain language constructs which cannot be
 * handled by our repair approach and its implementation.
 */
object ELTBoxExpressivityChecker {

  def check(ontology: OWLOntology): Boolean = {
    ontology.axioms(Imports.INCLUDED).toScala(LazyList).foldLeft(true)(_ && checkAxiom(_))
  }

  def checkAxiom(axiom: OWLAxiom): Boolean = {
    axiom match
      case Declaration(annotations, entity) =>
        annotations.foldLeft(true)(_ && checkAnnotation(_))
      case SubClassOf(annotations, subClass, superClass) =>
        annotations.foldLeft(true)(_ && checkAnnotation(_))
          && checkClassExpression(subClass)
          && checkClassExpression(superClass)
      case EquivalentClasses(annotations, operands) =>
        annotations.foldLeft(true)(_ && checkAnnotation(_))
          && operands.foldLeft(true)(_ && checkClassExpression(_))
      case ObjectPropertyDomain(annotations, property, filler) =>
        annotations.foldLeft(true)(_ && checkAnnotation(_))
          && checkObjectPropertyExpression(property)
          && checkClassExpression(filler)
      case _ =>
        false
  }

  def checkClassExpression(concept: OWLClassExpression): Boolean = {
    concept match
      case c @ Class(_) =>
        !(c equals OWLNothing)
      case ObjectIntersectionOf(operands) =>
        operands.foldLeft(true)(_ && checkClassExpression(_))
      case ObjectSomeValuesFrom(property, filler) =>
        checkObjectPropertyExpression(property)
          && checkClassExpression(filler)
      case ObjectMinCardinality(num, property, filler) =>
        (num equals 0)
          || ((num equals 1)
               && checkObjectPropertyExpression(property)
               && checkClassExpression(filler))
      case _ =>
        false
  }

  def checkObjectPropertyExpression(property: OWLObjectPropertyExpression): Boolean = {
    property match
      case r @ ObjectProperty(_) =>
        !(r equals OWLRDFVocabulary.OWL_TOP_OBJECT_PROPERTY)
          && !(r equals OWLRDFVocabulary.OWL_BOTTOM_OBJECT_PROPERTY)
      case _ =>
        false
  }

  def checkAnnotation(annotation: OWLAnnotation): Boolean = {
    true
  }

  def normalizeClassExpression(classExpression: OWLClassExpression): OWLClassExpression = {
    classExpression match
      case c @ Class(_) => c
      case ObjectIntersectionOf(operands) =>
        if (operands.isEmpty) OWLThing
        else operands.map(normalizeClassExpression).reduceLeft(_ and _)
      case ObjectSomeValuesFrom(property, filler) =>
        property some normalizeClassExpression(filler)
      case ObjectMinCardinality(num, property, filler) if num equals 0 =>
        OWLThing
      case ObjectMinCardinality(num, property, filler) if num equals 1 =>
        property some normalizeClassExpression(filler)
      case _ =>
        throw new IllegalArgumentException("Only 𝓔𝓛 concepts are supported.")
  }

  def getSubClassOfAxioms(ontology: OWLOntology): LazyList[OWLSubClassOfAxiom] = {
    ontology.axioms(Imports.INCLUDED).toScala(LazyList).flatMap[OWLSubClassOfAxiom] {
      case SubClassOf(_, subClass, superClass) =>
        Set(normalizeClassExpression(subClass) SubClassOf normalizeClassExpression(superClass))
      case EquivalentClasses(_, operands) =>
        for (subClass <- operands; superClass <- operands if !(subClass equals superClass))
          yield normalizeClassExpression(subClass) SubClassOf normalizeClassExpression(superClass)
      case ObjectPropertyDomain(_, property, filler) =>
        Set((property some OWLThing) SubClassOf normalizeClassExpression(filler))
      case _ =>
        Set.empty[OWLSubClassOfAxiom]
    }
  }

}