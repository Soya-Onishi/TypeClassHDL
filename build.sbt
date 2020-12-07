import java.io.File

enablePlugins(Antlr4Plugin)

lazy val antlr4Settings = Seq(
  antlr4Version in Antlr4 := "4.7.2",
  antlr4GenVisitor in Antlr4 := true,
  antlr4PackageName in Antlr4 := Some("tchdl.antlr"),
  javaSource in Antlr4 := (sourceManaged in Compile).value,
)

lazy val compilerSettings = Seq(
  libraryDependencies ++= Seq(
    "edu.berkeley.cs" %% "treadle" % "1.3.1" % "test",
    "edu.berkeley.cs" %% "firrtl" % "1.4.1",
    "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  ),
  scalacOptions ++= Seq(
    "-language:higherKinds"
  ),
  assemblyJarName in assembly := "tchdl.jar",
  assemblyOutputPath in assembly := new File("./bin/tchdl.jar"),
  test in assembly := {}
)

lazy val commonSettings = Seq(
  version := "0.1",
  scalaVersion := "2.12.11",
  libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  ),
)

lazy val compiler = (project in file("."))
  .settings(
    name := "compiler",
    commonSettings,
    compilerSettings,
    antlr4Settings,
  )
