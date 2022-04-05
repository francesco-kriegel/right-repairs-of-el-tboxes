package de.tu_dresden.inf.lat.repairs

import org.phenoscape.scowl.*
import org.semanticweb.elk.owlapi.ElkReasonerFactory
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.{OWLClass, OWLClassExpression, OWLSubClassOfAxiom}

import scala.collection.mutable
import scala.jdk.StreamConverters.*

class ELSubsumptionReasoner(axioms: Iterable[OWLSubClassOfAxiom],
                            classExpressions: Iterable[OWLClassExpression],
                            allowNewClassExpressions: Boolean = true)
  extends PartialOrdering[OWLClassExpression] {

  private val ontology = OWLManager.createOWLOntologyManager().createOntology()
  axioms.foreach(ontology.addAxiom)

  def addAxiom(axiom: OWLSubClassOfAxiom): Unit = {
    ontology.addAxiom(axiom)
  }

  def removeAxiom(axiom: OWLSubClassOfAxiom): Unit = {
    ontology.removeAxiom(axiom)
  }

  private val representativeOf = mutable.HashMap[OWLClassExpression, OWLClass]()
  private val representativeFor = mutable.HashMap[OWLClass, OWLClassExpression]()

  private def addRepresentative(classExpression: OWLClassExpression): Unit = {
    val representative =
      classExpression match
        case c @ Class(_) => c
        case _ => Class("internal_representative_class_for#" + classExpression)
    representativeOf(classExpression) = representative
    representativeFor(representative) = classExpression
    if (!(classExpression equals representative))
      ontology.addAxiom(EquivalentClasses(representative, classExpression))
  }

  private def hasRepresentative(classExpression: OWLClassExpression): Boolean = {
    representativeOf contains classExpression
  }

  private def ensureHasRepresentative(classExpression: OWLClassExpression): Unit = {
    representativeOf.synchronized {
      if (!hasRepresentative(classExpression))
        if (allowNewClassExpressions)
          addRepresentative(classExpression)
        else
          throw new RuntimeException("No new class expressions in the reasoner are allowed.")
    }
  }

  representativeOf(OWLThing) = OWLThing
  representativeFor(OWLThing) = OWLThing
  classExpressions.foreach(addRepresentative)

  private val elkReasoner = ElkReasonerFactory().createNonBufferingReasoner(ontology)
  elkReasoner.precomputeInferences()
  elkReasoner.flush()

  def dispose(): Unit = {
    elkReasoner.dispose()
  }

  def entails(subClassOfAxiom: OWLSubClassOfAxiom): Boolean = {
    isSubsumedBy(subClassOfAxiom.getSubClass, subClassOfAxiom.getSuperClass)
  }

  def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(superClassExpression)
    subsumers(subClassExpression).contains(superClassExpression)
  }

  def subsumers(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    ensureHasRepresentative(classExpression)
    java.util.stream.Stream.concat(
      elkReasoner.equivalentClasses(representativeOf(classExpression)),
      elkReasoner.superClasses(representativeOf(classExpression))
    ).toScala(LazyList).map(representativeFor)
  }

  def subsumees(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    ensureHasRepresentative(classExpression)
    java.util.stream.Stream.concat(
      elkReasoner.equivalentClasses(representativeOf(classExpression)),
      elkReasoner.subClasses(representativeOf(classExpression))
    ).toScala(LazyList).filterNot(_ equals OWLNothing).map(representativeFor)
  }

  override def tryCompare(x: OWLClassExpression, y: OWLClassExpression): Option[Int] = {
    if (lt(x, y))          Some(-1)
    else if (equiv(x, y))  Some(0)
    else if (gt(x, y))     Some(1)
    else                   None
  }

  override def lteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || lt(x, y)

  override def gteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || gt(x, y)

  override def lt(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.superClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

  override def gt(x: OWLClassExpression, y: OWLClassExpression): Boolean = lt(y, x)

  override def equiv(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.equivalentClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

}
