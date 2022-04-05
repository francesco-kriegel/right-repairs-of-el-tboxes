package de.tu_dresden.inf.lat.repairs

import Util.*

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.io.FileDocumentTarget
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLOntology, OWLSubClassOfAxiom}

import java.io.File
import scala.annotation.tailrec
import scala.collection.mutable
import scala.io.StdIn.{readInt, readLine}
import scala.jdk.StreamConverters.*

object Main {

  def main(args: Array[String]): Unit = {

    val manager = OWLManager.createOWLOntologyManager()

    val tboxOntologyFile = readInputFileName("Enter file name of ontology: ")
    val tboxOntology = manager.loadOntologyFromOntologyDocument(tboxOntologyFile)
    if (!ELTBoxExpressivityChecker.check(tboxOntology)) {
      System.err.println("The ontology contains unsupported language constructs.")
      // System.exit(1)
    }
    println()

    val tbox = ELTBoxExpressivityChecker.getSubClassOfAxioms(tboxOntology).toSet
    println("The loaded ontology contains the following concept inclusions:")
    tbox.foreach(axiom => println(axiom.toDLString))
    println()

    val requestOntologyFile = readInputFileName("Enter file name of repair request: ")
    val requestOntology = manager.loadOntologyFromOntologyDocument(requestOntologyFile)
    if (!ELTBoxExpressivityChecker.check(requestOntology)) {
      System.err.println("The repair request contains unsupported language constructs.")
      System.exit(1)
    }
    println()

    val request = ELTBoxExpressivityChecker.getSubClassOfAxioms(requestOntology).toSet
    println("The loaded repair request contains the following unwanted consequences:")
    request.foreach(axiom => println(axiom.toDLString))
    println()

    val message =
      "Which of the following repair methods should be used?\n" +
        "1: right repair\n" +
        "2: saturated right repair, with fresh concept names\n" +
        "3: saturated right repair, unraveled up to a role-depth bound\n"
    val method =
      readIntInRange(message, 1, 3) match
        case 1 => RightRepair()
        case 2 => SaturatedRightRepairWithFreshConceptNames()
        case 3 =>
          val roleDepth = readIntInRange("Please specify the role-depth bound: ", 0, Int.MaxValue)
          SaturatedRightRepairUnfoldedUpToRoleDepth(roleDepth)
    println()

    print("Subconcepts: ")
    val subConcepts =
      tbox.flatMap(_.nestedClassExpressions.toScala(LazyList)) concat
        request.flatMap(_.nestedClassExpressions.toScala(LazyList))
    println(subConcepts.size)
    // println()

    val tboxReasoner = ELSubsumptionReasoner(tbox, subConcepts, false)
    val emptyReasoner = ELSubsumptionReasoner(Set(), subConcepts, false)

    print("Possible seed axioms: ")
    val seedAxioms =
      tbox.map(_.getSubClass)
        .flatMap(x => subConcepts.filter(_.isAtom).map(y => x SubClassOf y))
        .filter(tboxReasoner.entails)
        .filterNot(emptyReasoner.entails)
    println(seedAxioms.size)
    println()

    def isSemanticallySmallerThan(classExpression1: OWLClassExpression, classExpression2: OWLClassExpression): Boolean = {
      (classExpression1 subsumes classExpression2 wrt emptyReasoner) ||
        classExpression2.conjunctSet().toScala(LazyList).exists {
          case ObjectSomeValuesFrom(_,filler) => isSemanticallySmallerThan(classExpression1, filler)
          case _ => false
        }
    }

    val seed = mutable.HashSet[OWLSubClassOfAxiom]()
    val seedReasoner = ELSubsumptionReasoner(Set(), subConcepts, true)
    seedAxioms.toList
      .sortWith((axiom1, axiom2) => isSemanticallySmallerThan(axiom1.getSubClass, axiom2.getSubClass))
      .foreach(seedAxiom => {
        if (!(seedReasoner entails seedAxiom)) {
          seedReasoner.addAxiom(seedAxiom)
          if (request.exists(seedReasoner entails _)) {
            seedReasoner.removeAxiom(seedAxiom)
          } else {
            println("Is the following concept inclusion valid?  Please answer with 'Yes' or 'No' (case-insensitive).")
            println(seedAxiom.toDLString)
            if (readLine().toLowerCase.startsWith("y"))
              seed.add(seedAxiom)
            else
              seedReasoner.removeAxiom(seedAxiom)
            println()
          }
        }
      })

    tboxReasoner.dispose()
    emptyReasoner.dispose()
    seedReasoner.dispose()

    print("Computing the induced repair... ")
    val repair = ELTBoxRightRepairer(ELTBoxRightRepairConfiguration(tbox, request, seed.toSet, method)).repair
    println("done!")
    println()

    println("The repair contains the following concept inclusions:")
    repair.foreach(axiom => println(axiom.toDLString))
    println()

    println("Should the repair be exported to a file?  Please answer with 'Yes' or 'No' (case-insensitive).")
    if (readLine().toLowerCase.startsWith("y")) {
      val repairOntologyFile = readOutputFileName("Enter file name of repair: ")
      println()

      val repairOntology = manager.createOntology()
      repair.foreach(repairOntology.addAxiom)
      manager.saveOntology(repairOntology, manager.getOntologyFormat(tboxOntology), FileDocumentTarget(repairOntologyFile))
      println("Successfully stored the repaired ontology in file " + repairOntologyFile)
    }

  }

  @tailrec
  def readInputFileName(message: String): File = {
    print(message)
    val file = new File(readLine())
    if (file.exists) {
      file
    } else {
      System.err.println("The file could not be found.")
      println()
      readInputFileName(message)
    }
  }

  @tailrec
  def readOutputFileName(message: String): File = {
    print(message)
    val file = new File(readLine())
    if (file.exists) {
      System.err.println("The file already exists.  Should it be overwritten?  Please answer with 'Yes' or 'No' (case-insensitive).")
      if (readLine().toLowerCase.startsWith("y")) {
        file
      } else {
        println()
        readOutputFileName(message)
      }
    } else {
      file
    }
  }

  @tailrec
  def readIntInRange(message: String, min: Int, max: Int): Int = {
    print(message)
    try {
      val number = readInt()
      if (number < min || number > max) throw IllegalArgumentException()
      else number
    } catch {
      case _: NumberFormatException | _: IllegalArgumentException =>
        System.err.println("Please enter a number between " + min + " and " + max + ".")
        println()
        readIntInRange(message, min, max)
    }
  }

}
