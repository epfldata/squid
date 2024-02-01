import sbt._
import sbt.Keys._

object Compiler extends AutoPlugin {
  override def trigger = allRequirements

  override def projectSettings: Seq[Def.Setting[_]] =
    Seq(
      libraryDependencies ++= (CrossVersion.partialVersion(scalaVersion.value) match {
        case Some((2, x)) if x < 13 =>
          Seq(
            compilerPlugin(("org.scalamacros" % "paradise" % "2.1.1" cross CrossVersion.full)),
            "org.scala-lang.modules" %% "scala-collection-compat" % "2.1.6"
          )
        case _ => Nil
      }),
      Compile / scalacOptions ++= (CrossVersion.partialVersion(scalaVersion.value) match {
        case Some((2, x)) if x >= 13 =>
          Seq("-Ymacro-annotations")
        case _ => Nil
      })
    )

}
