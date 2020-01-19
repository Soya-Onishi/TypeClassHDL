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
)


lazy val root = (project in file("."))
  .settings(
    commonSettings,
    antlr4Settings,
    name := "root",
  )
