ThisBuild / organization := "de.tu_dresden.inf.lat"
ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.1.1"

lazy val root = (project in file("."))
  .settings(
    name := "right-repairs-of-el-tboxes"
    // , idePackagePrefix := "de.tu_dresden.inf.lat.repairs"
  )

resolvers +=
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies += "net.sourceforge.owlapi" % "owlapi-distribution" % "5.1.20"
libraryDependencies += "org.phenoscape" %% "scowl-owlapi5" % "1.4.1"
libraryDependencies += "org.semanticweb.elk" % "elk-owlapi5" % "0.5.0-SNAPSHOT"

ThisBuild / assemblyMergeStrategy  := {
  case PathList("module-info.class") => MergeStrategy.discard
  case x if x.endsWith("/module-info.class") => MergeStrategy.discard
  case x =>
    val oldStrategy = (ThisBuild / assemblyMergeStrategy).value
    oldStrategy(x)
}

Compile / mainClass := Some("de.tu_dresden.inf.lat.repairs.Main")
//assembly / mainClass := Some("de.tu_dresden.inf.lat.repairs.Main")