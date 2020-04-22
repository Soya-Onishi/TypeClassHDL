enablePlugins(Antlr4Plugin)

lazy val antlr4Settings = Seq(
  antlr4Version in Antlr4 := "4.7.2",
  antlr4GenVisitor in Antlr4 := true,
  antlr4PackageName in Antlr4 := Some("tchdl.antlr"),
  javaSource in Antlr4 := (sourceManaged in Compile).value,
)

lazy val commonSettings = Seq(
  version := "0.1",
  scalaVersion := "2.13.1",
  libraryDependencies ++= Seq(
    "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  ),
  scalacOptions ++= Seq(
    "-Ymacro-annotations"
  )
)


lazy val root = (project in file("."))
  .settings(
    commonSettings,
    antlr4Settings,
    name := "root",
  ).dependsOn(macros)


lazy val macros = (project in file("macros"))
  .settings(
    commonSettings,
    name := "macros",
    libraryDependencies ++= Seq(
      scalaOrganization.value % "scala-reflect" % scalaVersion.value % "provided",
    )
  )
