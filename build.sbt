ThisBuild / organization := "de.tu_dresden.inf.lat"
ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.1.1"

lazy val root = (project in file("."))
  .settings(
    name := "right-repairs-of-el-tboxes",
    idePackagePrefix := Some("de.tu_dresden.inf.lat.repairs")
  )

resolvers +=
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies += "net.sourceforge.owlapi" % "owlapi-distribution" % "5.1.20"
libraryDependencies += "org.phenoscape" %% "scowl-owlapi5" % "1.4.1"
libraryDependencies += "org.semanticweb.elk" % "elk-owlapi5" % "0.5.0-SNAPSHOT"
