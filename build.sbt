enablePlugins(Antlr4Plugin)

lazy val antlr4Settings = Seq(
  antlr4Version in Antlr4 := "4.7.2",
  antlr4GenVisitor := true,
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
