lazy val commonSettings = Seq(
  version := "0.1",
  scalaVersion := "2.13.1",
)


lazy val root = (project in file("."))
  .settings(
    commonSettings,
    name := "root",
  )
