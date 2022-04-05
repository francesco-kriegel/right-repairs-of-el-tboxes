package de.tu_dresden.inf.lat.repairs

import Util.*

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLClass, OWLClassExpression, OWLObjectProperty, OWLSubClassOfAxiom}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.jdk.StreamConverters.*

class ELTBoxRightRepairer(private val configuration: ELTBoxRightRepairConfiguration) {

  private val subConcepts: Set[OWLClassExpression] =
    configuration.tbox.flatMap(_.nestedClassExpressions.toScala(LazyList)) concat
      configuration.request.flatMap(_.nestedClassExpressions.toScala(LazyList))

  private val tboxReasoner: ELSubsumptionReasoner =
    ELSubsumptionReasoner(configuration.tbox, subConcepts, false)
  private val seedReasoner: ELSubsumptionReasoner =
    ELSubsumptionReasoner(configuration.seed, subConcepts, false)
  private val emptyReasoner: ELSubsumptionReasoner =
    ELSubsumptionReasoner(Set(), subConcepts)

  lazy val repair: Set[OWLSubClassOfAxiom] = computeRepair()

  private def computeRepair(): Set[OWLSubClassOfAxiom] = {
    if (configuration.request.exists(seedReasoner.entails))
      throw new RuntimeException("The seed entails at least one unwanted consequence!")
    val repair =
      configuration.method match {
        case RightRepair() =>
          configuration.tbox.map(modifySubClassOfAxiom)
        case SaturatedRightRepairUnfoldedUpToRoleDepth(roleDepth) =>
          configuration.tbox.map(_.getSubClass).map(getRepairedSubClassOfAxiomForPremise(roleDepth))
        case SaturatedRightRepairWithFreshConceptNames() =>
          constructRepairWithFreshConceptNames()
      }
    val reasoner = ELSubsumptionReasoner(repair, repair.flatMap(_.nestedClassExpressions.toScala(LazyList)))
    if (configuration.request.exists(reasoner.entails))
      throw new RuntimeException("Something went wrong!")
    reasoner.dispose()
    tboxReasoner.dispose()
    seedReasoner.dispose()
    emptyReasoner.dispose()
    repair
  }

  /******************
  *                 *
  *  Right repairs  *
  *                 *
  ******************/

  private def modifySubClassOfAxiom(axiom: OWLSubClassOfAxiom): OWLSubClassOfAxiom = {
    val maximalModificationType =
      maximalElements(
        tboxReasoner
          .subsumers(axiom.getSuperClass)
          .filter(_.isAtom)
          .filterNot(axiom.getSubClass isSubsumedBy _ wrt seedReasoner),
        emptyReasoner)
    axiom.getSubClass SubClassOf modifyClassExpression(axiom.getSuperClass, maximalModificationType)
  }

  private def modifyClassExpression(classExpression: OWLClassExpression, modificationType: ModificationType): OWLClassExpression = {
    if (emptyReasoner entails (OWLThing SubClassOf classExpression))
      OWLThing
    else {
      val modifiedClassExpression =
        classExpression.topLevelConjuncts()
          .foldLeft[OWLClassExpression](OWLThing)((result, conjunct) => {
            conjunct match
              case c @ Class(_) if !(modificationType contains c) =>
                result and c
              case ObjectSomeValuesFrom(property @ ObjectProperty(_), filler) =>
                getMinimalModificationTypesCovering(Succ(modificationType, property, filler))
                  .map(property some modifyClassExpression(filler,_))
                  .foldLeft(result)(_ and _)
              case _ =>
                result
          })
//      reduce(modifiedClassExpression)
      modifiedClassExpression.reduced
    }
  }

  /*****************************************
  *                                        *
  *  Saturated right repairs               *
  *  (unraveled up to a role-depth bound)  *
  *                                        *
  *****************************************/

  private def getRepairedSubClassOfAxiomForPremise(roleDepth: Int)(premise: OWLClassExpression): OWLSubClassOfAxiom = {
    val maximalModificationType =
      maximalElements(
        tboxReasoner
          .subsumers(premise)
          .filter(_.isAtom)
          .filterNot(premise isSubsumedBy _ wrt seedReasoner),
        emptyReasoner)
    premise SubClassOf unfold(CountermodelObject(premise, maximalModificationType), roleDepth)
  }

  private def unfold(countermodelObject: CountermodelObject, roleDepth: Int): OWLClassExpression = {
//    val conceptNames: Set[OWLClassExpression] =
//      subConcepts filter {
//        case c @ Class(_) if !(c equals OWLThing) => true
//        case _ => false
//      } filter {
//        countermodelObject.objectInCanonicalModel isSubsumedBy _ wrt tboxReasoner
//      } diff {
//        countermodelObject.modificationType
//      }
    val conceptNames =
      tboxReasoner.subsumers(countermodelObject.objectInCanonicalModel) filter {
        case c @ Class(_) if !(c equals OWLThing) => true
        case _ => false
      } diff {
        countermodelObject.modificationType.toSeq
      }
    val topLevelConjuncts =
      if (roleDepth == 0)
        conceptNames
      else
        conceptNames ++
          minimalElements(
            getSuccessors(countermodelObject)
              .map(successor => successor._1 some unfold(successor._2, roleDepth - 1)),
            emptyReasoner
          )
    if (topLevelConjuncts.isEmpty) OWLThing
    else topLevelConjuncts reduceLeft { _ and _ }
  }

  /*******************************
  *                              *
  *  Saturated right repairs     *
  *  (with fresh concept names)  *
  *                              *
  *******************************/

  private def constructRepairWithFreshConceptNames(): Set[OWLSubClassOfAxiom] = {
    val repair = mutable.Set[OWLSubClassOfAxiom]()
    val freshConceptNames = mutable.Map[CountermodelObject, OWLClass]()
    def hasBeenProcessed(countermodelObject: CountermodelObject): Boolean = {
      freshConceptNames contains countermodelObject
    }
    def freshConceptNameFor(countermodelObject: CountermodelObject): OWLClass = {
      freshConceptNames(countermodelObject)
    }
    val forbiddenNames =
      subConcepts filter {
        case c @ Class(_) if !(c equals OWLThing) => true
        case _ => false
      }
    val nextInt = { var n = 0; () => { n = n + 1; n } }
    @tailrec
    def nextAdmissibleConceptName(): OWLClass = {
      val nextConceptName: OWLClass = Class("X" + nextInt())
      if (forbiddenNames contains nextConceptName)
        nextAdmissibleConceptName()
      else
        nextConceptName
    }
    def addFreshConceptNameFor(countermodelObject: CountermodelObject): OWLClass = {
      val freshConceptName: OWLClass = nextAdmissibleConceptName()
      freshConceptNames.put(countermodelObject, freshConceptName)
      freshConceptName
    }
    def addToRepair(countermodelObject: CountermodelObject): Unit = {
//      subConcepts filter {
//        case c @ Class(_) if !(c equals OWLThing) => true
//        case _ => false
//      } filter {
//        countermodelObject.objectInCanonicalModel isSubsumedBy _ wrt tboxReasoner
//      } diff {
//        countermodelObject.modificationType
//      } foreach {
//        c => repair.add(freshConceptNameFor(countermodelObject) SubClassOf c)
//      }
      tboxReasoner.subsumers(countermodelObject.objectInCanonicalModel) filter {
        case c @ Class(_) if !(c equals OWLThing) => true
        case _ => false
      } diff {
        countermodelObject.modificationType.toSeq
      } map {
        freshConceptNameFor(countermodelObject) SubClassOf _
      } foreach {
        repair.add
      }
      getSuccessors(countermodelObject) foreach {
        case (property, successorObject) =>
          if (hasBeenProcessed(successorObject)) {
            repair.add(freshConceptNameFor(countermodelObject) SubClassOf (property some freshConceptNameFor(successorObject)))
          } else {
            val freshConceptName = addFreshConceptNameFor(successorObject)
            repair.add(freshConceptNameFor(countermodelObject) SubClassOf (property some freshConceptName))
            addToRepair(successorObject)
          }
      }
    }
    configuration.tbox.map(_.getSubClass).foreach(premise => {
      val maximalModificationType =
        maximalElements(
          tboxReasoner
            .subsumers(premise)
            .filter(_.isAtom)
            .filterNot(premise isSubsumedBy _ wrt seedReasoner),
          emptyReasoner)
      val countermodelObject = CountermodelObject(premise, maximalModificationType)
      val freshConceptName = addFreshConceptNameFor(countermodelObject)
      repair.add(premise SubClassOf freshConceptName)
      addToRepair(countermodelObject)
    })
    repair.toSet
  }

  private def getSuccessors(countermodelObject: CountermodelObject): LazyList[(OWLObjectProperty,CountermodelObject)] = {
//    subConcepts flatMap {
//      case existentialRestriction @ ObjectSomeValuesFrom(property @ ObjectProperty(_), filler)
//        if countermodelObject.objectInCanonicalModel isSubsumedBy existentialRestriction wrt tboxReasoner =>
//        getMinimalModificationTypesCovering(Succ(countermodelObject.modificationType, property, filler))
//          .map(minimalModificationType => (property, CountermodelObject(filler, minimalModificationType)))
//      case _ => Set.empty
//    }
    tboxReasoner.subsumers(countermodelObject.objectInCanonicalModel) flatMap {
      case existentialRestriction @ ObjectSomeValuesFrom(property @ ObjectProperty(_), filler) =>
        getMinimalModificationTypesCovering(Succ(countermodelObject.modificationType, property, filler))
          .map(minimalModificationType => (property, CountermodelObject(filler, minimalModificationType)))
      case _ => Set.empty
    }
  }

  /********************
  *                   *
  *  Utility methods  *
  *                   *
  ********************/

  private type ModificationType = Set[OWLClassExpression]

  private implicit class ImplicitModificationType(modificationType: ModificationType) {

    def isCoveredBy(other: ModificationType): IsCoveredByReasonerRequest =
      IsCoveredByReasonerRequest(modificationType, other)

    def covers(other: ModificationType): IsCoveredByReasonerRequest =
      IsCoveredByReasonerRequest(other, modificationType)

  }

  private class IsCoveredByReasonerRequest(modType1: ModificationType, modType2: ModificationType) {

    def wrt(reasoner: ELSubsumptionReasoner): Boolean =
//      modType1.forall(classExpression1 =>
//        modType2.exists(classExpression2 =>
//          classExpression1 isSubsumedBy classExpression2 wrt reasoner))
      modType1.forall(reasoner.subsumers(_).exists(modType2.contains))

  }

  private val modTypeOrdering = new PartialOrdering[ModificationType]() {

    def lteq(x: ModificationType, y: ModificationType): Boolean =
      x isCoveredBy y wrt emptyReasoner

    def tryCompare(x: ModificationType, y: ModificationType): Option[Int] =
      val a = lteq(x,y)
      val b = lteq(y,x)
      if (a && b)  Some(0)
      else if (a)  Some(-1)
      else if (b)  Some(1)
      else         None

  }

  private def Succ(modificationType: ModificationType, property: OWLObjectProperty, objectInCanonicalModel: OWLClassExpression): Set[OWLClassExpression] = {
    for (ObjectSomeValuesFrom(_property @ ObjectProperty(_), filler) <- modificationType
         if (property equals _property) && (objectInCanonicalModel isSubsumedBy filler wrt tboxReasoner))
    yield filler
  }

  private def getMinimalModificationTypesCovering(classExpressions: Set[OWLClassExpression]): Set[ModificationType] = {
    val initialModTypes =
      classExpressions.foldLeft[Set[Set[OWLClassExpression]]](Set(Set()))((result, classExpression) => {
        if (classExpression.topLevelConjuncts().isEmpty)
          Set()
        else
          result.flatMap(set => classExpression.topLevelConjuncts().map(set + _))
      })
    val queue = mutable.Queue[ModificationType]()
    queue ++= initialModTypes
    val respectingModTypes = mutable.HashSet[ModificationType]()
    while (queue.nonEmpty) {
      val modType = queue.dequeue()
//      val nonCoveredSubConcept = subConcepts.find(subConcept =>
//        (Set(subConcept) isCoveredBy modType wrt seedReasoner) &&
//          !(Set(subConcept) isCoveredBy modType wrt emptyReasoner))
      val nonCoveredSubConcept =
        modType.flatMap(seedReasoner.subsumees)
//          .find(subConcept => !(Set(subConcept) isCoveredBy modType wrt emptyReasoner))
          .find(subConcept => emptyReasoner.subsumers(subConcept).forall(!modType.contains(_)))
      if (nonCoveredSubConcept.isDefined)
        queue ++= nonCoveredSubConcept.get.topLevelConjuncts().map(modType + _)
      else
        respectingModTypes += maximalElements(modType, emptyReasoner)
    }
    minimalElements(respectingModTypes, modTypeOrdering)
  }

  private class CountermodelObject(val objectInCanonicalModel: OWLClassExpression, val modificationType: ModificationType) {
    override def toString: String =
      "⟪ " + objectInCanonicalModel.toDLString + " ; " + {
        if (modificationType.isEmpty) "∅"
        else "{ " + modificationType.head.toDLString +
          modificationType.tail.foldLeft("")((str, atom) => str + ", " + atom.toDLString) + " }"
      } + " ⟫"
    override def equals(other: Any): Boolean =
      other.isInstanceOf[CountermodelObject] &&
        (other.asInstanceOf[CountermodelObject].objectInCanonicalModel equals objectInCanonicalModel) &&
        (other.asInstanceOf[CountermodelObject].modificationType equals modificationType)
    override def hashCode(): Int =
      17 * objectInCanonicalModel.hashCode + 43 * modificationType.hashCode
  }

//  def reduce(classExpression: OWLClassExpression): OWLClassExpression = {
//    if (classExpression subsumes OWLThing wrt emptyReasoner)
//      OWLThing
//    else
//      minimalElements(
//        classExpression.topLevelConjuncts().map {
//          case ObjectSomeValuesFrom(property, filler) => property some reduce(filler)
//          case c @ Class(_)                           => c
//        },
//        emptyReasoner
//      ) reduceLeft { _ and _ }
//  }

}

class ELTBoxRightRepairConfiguration(val tbox: Set[OWLSubClassOfAxiom],
                                     val request: Set[OWLSubClassOfAxiom],
                                     val seed: Set[OWLSubClassOfAxiom],
                                     val method: ELTBoxRightRepairMethod = RightRepair()
                                    ) {}

trait ELTBoxRightRepairMethod
case class RightRepair() extends ELTBoxRightRepairMethod
case class SaturatedRightRepairUnfoldedUpToRoleDepth(roleDepth: Int) extends ELTBoxRightRepairMethod
case class SaturatedRightRepairWithFreshConceptNames() extends ELTBoxRightRepairMethod
