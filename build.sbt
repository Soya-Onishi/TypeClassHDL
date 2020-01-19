enablePlugins(Antlr4Plugin)

lazy val commonSettings = Seq(
  version := "0.1",
  scalaVersion := "2.13.1",
  antlr4Version in Antlr4 := "4.7.2",
  antlr4GenVisitor := true,
)


lazy val root = (project in file("."))
  .settings(
    commonSettings,
    name := "root",
  )
