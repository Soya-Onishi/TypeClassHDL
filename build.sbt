enablePlugins(Antlr4Plugin)

lazy val antlr4Settings = Seq(
  antlr4Version in Antlr4 := "4.7.2",
  antlr4GenVisitor in Antlr4 := true,
  antlr4PackageName in Antlr4 := Some("tchdl.antlr"),
  javaSource in Antlr4 := (sourceManaged in Compile).value,
)

lazy val commonSettings = Seq(
  version := "0.1",
  scalaVersion := "2.12.11",
  libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value,
    "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  ),
  scalacOptions ++= Seq(
    "-language:higherKinds"
  )
)

lazy val compiler = (project in file("."))
  .settings(
    name := "compiler",
    commonSettings,
    antlr4Settings,
  )
