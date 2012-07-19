import AssemblyKeys._

name := "ts0"

organization := "uk.ac.gla.dcs"

version := "0"

resolvers ++= Seq( 
  "Sonatype OSS" at "https://oss.sonatype.org/content/repositories/releases/",
  "artifactory" at 
  	"http://scalasbt.artifactoryonline.com/scalasbt/sbt-plugin-releases"
)

scalaVersion := "2.9.2"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.8" % "test",
  "com.googlecode.kiama" %% "kiama" % "1.3.0",
  "jline" % "jline" % "2.7"
)

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.8.3")

assemblySettings

mainClass in assembly := Some("uk.ac.gla.dcs.ts0.Driver")