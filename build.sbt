name := "ts0"

organization := "uk.ac.gla.dcs"

version := "0"

resolvers += "Sonatype OSS" at 
  "https://oss.sonatype.org/content/repositories/releases/"

scalaVersion := "2.9.2"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.8" % "test",
  "com.googlecode.kiama" %% "kiama" % "1.3.0"
)