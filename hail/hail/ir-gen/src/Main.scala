import scala.annotation.nowarn
import scala.language.implicitConversions

import mainargs.{main, ParserForMethods}

sealed abstract class Trait(val name: String)

object Trivial extends Trait("TrivialIR")
object BaseRef extends Trait("BaseRef")
final case class Typed(typ: String) extends Trait(s"TypedIR[$typ]")
object NDArray extends Trait("NDArrayIR")

final case class Apply(missingnessAware: Boolean = false)
    extends Trait(
      s"AbstractApplyNode[UnseededMissingness${if (missingnessAware) "Aware" else "Oblivious"}JVMFunction]"
    )

case class NChildren(static: Int = 0, dynamic: String = "") {
  def +(other: NChildren): NChildren = NChildren(
    static = static + other.static,
    dynamic = if (dynamic.isEmpty) other.dynamic else s"$dynamic + ${other.dynamic}",
  )
}

sealed abstract class ChildrenSeq {
  def asDyn: ChildrenSeq.Dynamic

  def ++(other: ChildrenSeq): ChildrenSeq = (this, other) match {
    case (ChildrenSeq.Static(Seq()), r) => r
    case (l, ChildrenSeq.Static(Seq())) => l
    case (ChildrenSeq.Static(l), ChildrenSeq.Static(r)) => ChildrenSeq.Static(l ++ r)
    case _ => ChildrenSeq.Dynamic(this.asDyn.children + " ++ " + other.asDyn.children)
  }
}

object ChildrenSeq {
  val empty: Static = Static(Seq.empty)

  final case class Static(children: Seq[String]) extends ChildrenSeq {
    def asDyn: Dynamic = Dynamic(s"FastSeq(${children.mkString(", ")})")

    override def toString: String = ???
  }

  final case class Dynamic(children: String) extends ChildrenSeq {
    def asDyn: Dynamic = this
  }
}

final case class NamedAttOrChildPack(
  name: String,
  pack: AttOrChildPack,
  isVar: Boolean = false,
  default: Option[String] = None,
) {
  def mutable: NamedAttOrChildPack = copy(isVar = true)
  def withDefault(value: String): NamedAttOrChildPack = copy(default = Some(value))

  def generateDeclaration: String =
    s"${if (isVar) "var " else ""}$name: ${pack.generateDeclaration}${default.map(d => s" = $d").getOrElse("")}"

  def constraints: Seq[String] = pack.constraints.map(_(name))
  def nChildren: NChildren = pack.nChildren(name)
  def childrenSeq: ChildrenSeq = pack.childrenSeq(name)
}

sealed abstract class AttOrChildPack {
  def * : AttOrChildPack = Collection(this)
  def + : AttOrChildPack = Collection(this, allowEmpty = false)
  def ? : AttOrChildPack = Optional(this)

  def generateDeclaration: String
  def constraints: Seq[String => String] = Seq.empty
  def nChildren: String => NChildren = _ => NChildren()
  def childrenSeq: String => ChildrenSeq
}

final case class Att(typ: String, override val constraints: Seq[String => String] = Seq.empty)
    extends AttOrChildPack {
  def withConstraint(c: String => String): Att = copy(constraints = constraints :+ c)

  override def generateDeclaration: String = typ
  override def childrenSeq: String => ChildrenSeq = _ => ChildrenSeq.empty
}

final case class Child(t: String = "IR") extends AttOrChildPack {
  override def generateDeclaration: String = t
  override def nChildren: String => NChildren = _ => NChildren(static = 1)
  override def childrenSeq: String => ChildrenSeq = x => ChildrenSeq.Static(Seq(x))
}

case object Binding extends AttOrChildPack {
  override def generateDeclaration: String = "Binding"
  override def nChildren: String => NChildren = _ => NChildren(static = 1)
  override def childrenSeq: String => ChildrenSeq = x => ChildrenSeq.Static(Seq(s"$x.value"))
}

final case class Optional(elt: AttOrChildPack) extends AttOrChildPack {
  override def generateDeclaration: String = s"Option[${elt.generateDeclaration}]"

  override def nChildren: String => NChildren = elt match {
    case Att(_, _) => _ => NChildren()
    case _ => opt => NChildren(dynamic = s"$opt.map(x => ${elt.nChildren("x")}).sum")
  }

  override def childrenSeq: String => ChildrenSeq = elt match {
    case Att(_, _) => _ => ChildrenSeq.empty
    case Child(_) => opt => ChildrenSeq.Dynamic(s"$opt.toSeq")
    case _ => opt =>
        ChildrenSeq.Dynamic(s"$opt.toSeq.flatMap(x => ${elt.childrenSeq("x").asDyn.children})")
  }
}

final case class Collection(elt: AttOrChildPack, allowEmpty: Boolean = true)
    extends AttOrChildPack {
  override def generateDeclaration: String = s"IndexedSeq[${elt.generateDeclaration}]"

  override def constraints: Seq[String => String] = {
    val nestedConstraints: Seq[String => String] = if (elt.constraints.nonEmpty)
      Seq(elts =>
        s"$elts.forall(x => ${elt.constraints.map(c => s"(${c("x")})").mkString(" && ")})"
      )
    else Seq()
    val nonEmptyConstraint: Seq[String => String] =
      if (allowEmpty) Seq() else Seq(x => s"$x.nonEmpty")
    nestedConstraints ++ nonEmptyConstraint
  }

  override def nChildren: String => NChildren = elt match {
    case Att(_, _) => _ => NChildren()
    case Child(_) => elts => NChildren(dynamic = s"$elts.size")
    case _ => elts => NChildren(dynamic = s"$elts.map(x => ${elt.nChildren("x")}).sum")
  }

  override def childrenSeq: String => ChildrenSeq = elt match {
    case Att(_, _) => _ => ChildrenSeq.empty
    case Child(_) => elts => ChildrenSeq.Dynamic(elts)
    case _ =>
      elts => ChildrenSeq.Dynamic(s"$elts.flatMap(x => ${elt.childrenSeq("x").asDyn.children})")
  }
}

final case class Tup(elts: AttOrChildPack*) extends AttOrChildPack {
  override def generateDeclaration: String =
    elts.map(_.generateDeclaration).mkString("(", ", ", ")")

  override def constraints: Seq[String => String] =
    elts.zipWithIndex.flatMap { case (elt, i) =>
      elt.constraints.map(c => (t: String) => c(s"$t._${i + 1}"))
    }

  override def nChildren: String => NChildren = t =>
    elts.zipWithIndex
      .map { case (elt, i) => elt.nChildren(s"$t._${i + 1}") }
      .foldLeft(NChildren())(_ + _)

  override def childrenSeq: String => ChildrenSeq =
    t =>
      elts
        .zipWithIndex.map { case (elt, i) => elt.childrenSeq(s"$t._${i + 1}") }
        .foldLeft[ChildrenSeq](ChildrenSeq.empty)(_ ++ _)
}

case class IR(
  name: String,
  attsAndChildren: Seq[NamedAttOrChildPack],
  traits: Seq[Trait] = Seq.empty,
  constraints: Seq[String] = Seq.empty,
  extraMethods: Seq[String] = Seq.empty,
  applyMethods: Seq[String] = Seq.empty,
  docstring: String = "",
) {
  def withTraits(newTraits: Trait*): IR = copy(traits = traits ++ newTraits)
  def withMethod(methodDef: String): IR = copy(extraMethods = extraMethods :+ methodDef)
  def withApply(methodDef: String): IR = copy(applyMethods = applyMethods :+ methodDef)
  def typed(typ: String): IR = withTraits(Typed(typ))
  def withConstraint(c: String): IR = copy(constraints = constraints :+ c)

  def withCompanionExtension: IR = withApply(
    s"implicit def toCompExt(comp: $name.type): ${name}Ext.type = ${name}Ext"
  )

  def withClassExtension: IR = withApply(
    s"implicit def toExt(obj: $name): ${name}Ext = new ${name}Ext(obj)"
  )

  def withDocstring(docstring: String): IR = copy(docstring = docstring)

  private def nChildren: NChildren = attsAndChildren.foldLeft(NChildren())(_ + _.nChildren)

  private def children: String =
    attsAndChildren.foldLeft[ChildrenSeq](ChildrenSeq.empty)(_ ++ _.childrenSeq).asDyn.children

  private def paramList = s"$name(${attsAndChildren.map(_.generateDeclaration).mkString(", ")})"

  private def classDecl =
    s"final case class $paramList extends IR" + traits.map(" with " + _.name).mkString

  private def classBody = {
    val extraMethods =
      this.extraMethods :+ s"override lazy val childrenSeq: IndexedSeq[BaseIR] = $children"
    val constraints = this.constraints ++ attsAndChildren.flatMap(_.constraints)
    if (constraints.nonEmpty || extraMethods.nonEmpty) {
      (
        " {" +
          (if (constraints.nonEmpty)
             constraints.map(c => s"  require($c)").mkString("\n", "\n", "\n")
           else "")
          + (
            if (extraMethods.nonEmpty)
              extraMethods.map("  " + _).mkString("\n", "\n", "\n")
            else ""
          )
          + "}"
      )
    } else ""
  }

  private def classDef =
    (if (docstring.nonEmpty) s"\n/** $docstring*/\n" else "") + classDecl + classBody

  private def companionBody = applyMethods.map("  " + _).mkString("\n")

  private def companionDef =
    if (companionBody.isEmpty) "" else s"object $name {\n$companionBody\n}\n"

  def generateDef: String = companionDef + classDef + "\n"
}

object Main {
  private def node(name: String, attsAndChildren: NamedAttOrChildPack*): IR =
    IR(name, attsAndChildren)

  implicit private def makeNamedPack(tup: (String, AttOrChildPack)): NamedAttOrChildPack =
    NamedAttOrChildPack(tup._1, tup._2)

  private def att(typ: String): Att = Att(typ)

  private val binding = Binding

  private def tup(elts: AttOrChildPack*): Tup = Tup(elts: _*)

  private def child = Child()

  abstract private class BaseImplicit(t: AttOrChildPack, defaultName: String) {
    implicit def makeNamedChild(tup: (String, this.type)): NamedAttOrChildPack =
      NamedAttOrChildPack(tup._1, t)

    implicit def makeDefaultNamedChild(x: this.type): NamedAttOrChildPack =
      makeNamedChild((defaultName, x))

    implicit def makeChild(x: this.type): AttOrChildPack = t
  }

  private object name extends BaseImplicit(Att("Name"), "name")
  private object key extends BaseImplicit(Att("IndexedSeq[String]"), "key")
  private object tableChild extends BaseImplicit(Child("TableIR"), "child")
  private object matrixChild extends BaseImplicit(Child("MatrixIR"), "child")
  private object blockMatrixChild extends BaseImplicit(Child("BlockMatrixIR"), "child")

  private val errorID = ("errorID", att("Int")).withDefault("ErrorIDs.NO_ERROR")

  private def _typ(t: String = "Type") = ("_typ", att(t))

  private val mmPerElt = ("requiresMemoryManagementPerElement", att("Boolean")).withDefault("false")

  private def allNodes: Seq[IR] = {
    // scalafmt: {}

    val r = Seq.newBuilder[IR]

    r += node("I32", ("x", att("Int"))).withTraits(Trivial)
    r += node("I64", ("x", att("Long"))).withTraits(Trivial)
    r += node("F32", ("x", att("Float"))).withTraits(Trivial)
    r += node("F64", ("x", att("Double"))).withTraits(Trivial)
    r += node("Str", ("x", att("String"))).withTraits(Trivial)
      .withMethod(
        "override def toString(): String = s\"\"\"Str(\"${StringEscapeUtils.escapeString(x)}\")\"\"\""
      ): @nowarn("msg=possible missing interpolator")
    r += node("True").withTraits(Trivial)
    r += node("False").withTraits(Trivial)
    r += node("Void").withTraits(Trivial)
    r += node("NA", _typ()).withTraits(Trivial)
    r += node("UUID4", ("id", att("String")))
      .withDocstring(
        """WARNING! This node can only be used when trying to append a one-off,
          |random string that will not be reused elsewhere in the pipeline.
          |Any other uses will need to write and then read again; this node is non-deterministic
          |and will not e.g. exhibit the correct semantics when self-joining on streams.
          |""".stripMargin
      )
      .withCompanionExtension

    r += node(
      "Literal",
      ("_typ", att("Type").withConstraint(self => s"!CanEmit($self)")),
      ("value", att("Annotation").withConstraint(self => s"$self != null")),
    )
      .withCompanionExtension
      .withMethod(
        """// expensive, for debugging
          |// require(SafeRow.isSafe(value))
          |// assert(_typ.typeCheck(value), s"literal invalid:\n  ${_typ}\n  $value")
          |""".stripMargin
      )

    r += node(
      "EncodedLiteral",
      (
        "codec",
        att("AbstractTypedCodecSpec").withConstraint(self =>
          s"!CanEmit($self.encodedVirtualType)"
        ),
      ),
      ("value", att("WrappedByteArrays").withConstraint(self => s"$self != null")),
    )
      .withCompanionExtension

    r += node("Cast", ("v", child), _typ())
    r += node("CastRename", ("v", child), _typ())

    r += node("IsNA", ("value", child))
    r += node("Coalesce", ("values", child.+))
    r += node("Consume", ("value", child))

    r += node("If", ("cond", child), ("cnsq", child), ("altr", child))
    r += node("Switch", ("x", child), ("default", child), ("cases", child.*))
      .withMethod("override lazy val size: Int = 2 + cases.length")

    r += node("Block", ("bindings", binding.*), ("body", child))
      .withMethod("override lazy val size: Int = bindings.length + 1")
      .withCompanionExtension

    r += node("Ref", name, _typ().mutable).withTraits(BaseRef)

    r += node(
      "TailLoop",
      name,
      ("params", tup(name, child).*),
      ("resultType", att("Type")),
      ("body", child),
    )
      .withDocstring(
        """Recur can't exist outside of loop. Loops can be nested, but we can't call outer
          |loops in terms of inner loops so there can only be one loop "active" in a given
          |context.
          |""".stripMargin
      )
      .withMethod("lazy val paramIdx: Map[Name, Int] = params.map(_._1).zipWithIndex.toMap")
    r += node("Recur", name, ("args", child.*), _typ().mutable).withTraits(BaseRef)

    r += node("RelationalLet", name, ("value", child), ("body", child))
    r += node("RelationalRef", name, _typ()).withTraits(BaseRef)

    r += node("ApplyBinaryPrimOp", ("op", att("BinaryOp")), ("l", child), ("r", child))
    r += node("ApplyUnaryPrimOp", ("op", att("UnaryOp")), ("x", child))
    r += node(
      "ApplyComparisonOp",
      ("op", att("ComparisonOp[_]")).mutable,
      ("l", child),
      ("r", child),
    )

    r += node("MakeArray", ("args", child.*), _typ("TArray")).withCompanionExtension
    r += node("MakeStream", ("args", child.*), _typ("TStream"), mmPerElt).withCompanionExtension
    r += node("ArrayRef", ("a", child), ("i", child), errorID)
    r += node(
      "ArraySlice",
      ("a", child),
      ("start", child),
      ("stop", child.?),
      ("step", child).withDefault("I32(1)"),
      errorID,
    )
    r += node("ArrayLen", ("a", child))
    r += node("ArrayZeros", ("length", child))
    r += node(
      "ArrayMaximalIndependentSet",
      ("edges", child),
      ("tieBreaker", tup(name, name, child).?),
    )

    r += node("StreamIota", ("start", child), ("step", child), mmPerElt)
      .withDocstring(
        """[[StreamIota]] is an infinite stream producer, whose element is an integer starting at
          |`start`, updated by `step` at each iteration. The name comes from APL:
          |[[https://stackoverflow.com/questions/9244879/what-does-iota-of-stdiota-stand-for]]
          |""".stripMargin
      )
    r += node("StreamRange", ("start", child), ("stop", child), ("step", child), mmPerElt, errorID)

    r += node("ArraySort", ("a", child), ("left", name), ("right", name), ("lessThan", child))
      .withCompanionExtension

    r += node("ToSet", ("a", child))
    r += node("ToDict", ("a", child))
    r += node("ToArray", ("a", child))
    r += node("CastToArray", ("a", child))
    r += node("ToStream", ("a", child), mmPerElt)
    r += node("GroupByKey", ("collection", child))

    r += node(
      "StreamBufferedAggregate",
      ("streamChild", child),
      ("initAggs", child),
      ("newKey", child),
      ("seqOps", child),
      name,
      ("aggSignature", att("IndexedSeq[PhysicalAggSig]")),
      ("bufferSize", att("Int")),
    )
    r += node(
      "LowerBoundOnOrderedCollection",
      ("orderedCollection", child),
      ("elem", child),
      ("onKey", att("Boolean")),
    )

    r += node("RNGStateLiteral")
    r += node("RNGSplit", ("state", child), ("dynBitstring", child))

    r += node("StreamLen", ("a", child))
    r += node("StreamGrouped", ("a", child), ("groupSize", child))
    r += node("StreamGroupByKey", ("a", child), key, ("missingEqual", att("Boolean")))
    r += node("StreamMap", ("a", child), name, ("body", child)).typed("TStream")
    r += node("StreamTakeWhile", ("a", child), ("elementName", name), ("body", child))
      .typed("TStream")
    r += node("StreamDropWhile", ("a", child), ("elementName", name), ("body", child))
      .typed("TStream")
    r += node("StreamTake", ("a", child), ("num", child)).typed("TStream")
    r += node("StreamDrop", ("a", child), ("num", child)).typed("TStream")

    r += node(
      "SeqSample",
      ("totalRange", child),
      ("numToSample", child),
      ("rngState", child),
      mmPerElt,
    )
      .typed("TStream")
      .withDocstring(
        """Generate, in ascending order, a uniform random sample, without replacement, of
          |numToSample integers in the range [0, totalRange)
          |""".stripMargin
      )

    r += node(
      "StreamDistribute",
      ("child", child),
      ("pivots", child),
      ("path", child),
      ("comparisonOp", att("ComparisonOp[_]")),
      ("spec", att("AbstractTypedCodecSpec")),
    )
      .withDocstring(
        """Take the child stream and sort each element into buckets based on the provided pivots.
          |The first and last elements of pivots are the endpoints of the first and last interval
          |respectively, should not be contained in the dataset.
          |""".stripMargin
      )

    r += node(
      "StreamWhiten",
      ("stream", child),
      ("newChunk", att("String")),
      ("prevWindow", att("String")),
      ("vecSize", att("Int")),
      ("windowSize", att("Int")),
      ("chunkSize", att("Int")),
      ("blockSize", att("Int")),
      ("normalizeAfterWhiten", att("Boolean")),
    )
      .typed("TStream")
      .withDocstring(
        """"Whiten" a stream of vectors by regressing out from each vector all components
          |in the direction of vectors in the preceding window. For efficiency, takes
          |a stream of "chunks" of vectors.
          |Takes a stream of structs, with two designated fields: `prevWindow` is the
          |previous window (e.g. from the previous partition), if there is one, and
          |`newChunk` is the new chunk to whiten.
          |""".stripMargin
      )

    r += node(
      "StreamZip",
      ("as", child.*),
      ("names", name.*),
      ("body", child),
      ("behavior", att("ArrayZipBehavior.ArrayZipBehavior")),
      errorID,
    )
      .typed("TStream")

    r += node("StreamMultiMerge", ("as", child.*), key).typed("TStream")

    r += node(
      "StreamZipJoinProducers",
      ("contexts", child),
      ("ctxName", name),
      ("makeProducer", child),
      key,
      ("curKey", name),
      ("curVals", name),
      ("joinF", child),
    )
      .typed("TStream")

    r += node(
      "StreamZipJoin",
      ("as", child.*),
      key,
      ("curKey", name),
      ("curVals", name),
      ("joinF", child),
    )
      .typed("TStream")
      .withDocstring(
        """The StreamZipJoin node assumes that input streams have distinct keys. If input streams do not
          |have distinct keys, the key that is included in the result is undefined, but is likely the
          |last.
          |""".stripMargin
      )

    r += node("StreamFilter", ("a", child), name, ("cond", child)).typed("TStream")
    r += node("StreamFlatMap", ("a", child), name, ("cond", child)).typed("TStream")

    r += node(
      "StreamFold",
      ("a", child),
      ("zero", child),
      ("accumName", name),
      ("valueName", name),
      ("body", child),
    )

    r += node(
      "StreamFold2",
      ("a", child),
      ("accum", tup(name, child).*),
      ("valueName", name),
      ("seq", child.*),
      ("result", child),
    )
      .withConstraint("accum.length == seq.length")
      .withMethod("val nameIdx: Map[Name, Int] = accum.map(_._1).zipWithIndex.toMap")
      .withCompanionExtension

    r += node(
      "StreamScan",
      ("a", child),
      ("zero", child),
      ("accumName", name),
      ("valueName", name),
      ("body", child),
    )
      .typed("TStream")

    r += node("StreamFor", ("a", child), ("valueName", name), ("body", child)).typed("TVoid.type")
    r += node("StreamAgg", ("a", child), name, ("query", child))
    r += node("StreamAggScan", ("a", child), name, ("query", child)).typed("TStream")

    r += node(
      "StreamLeftIntervalJoin",
      ("left", child),
      ("right", child),
      ("lKeyFieldName", att("String")),
      ("rIntervalFieldName", att("String")),
      ("lname", name),
      ("rname", name),
      ("body", child),
    )
      .typed("TStream")

    r += node(
      "StreamJoinRightDistinct",
      ("left", child),
      ("right", child),
      ("lKey", att("IndexedSeq[String]")),
      ("rKey", att("IndexedSeq[String]")),
      ("l", name),
      ("r", name),
      ("joinF", child),
      ("joinType", att("String")),
    )
      .typed("TStream").withClassExtension

    r += node(
      "StreamLocalLDPrune",
      ("child", child),
      ("r2Threshold", child),
      ("windowSize", child),
      ("maxQueueSize", child),
      ("nSamples", child),
    )
      .typed("TStream")

    r += node("MakeNDArray", ("data", child), ("shape", child), ("rowMajor", child), errorID)
      .withTraits(NDArray).withCompanionExtension
    r += node("NDArrayShape", ("nd", child))
    r += node("NDArrayReshape", ("nd", child), ("shape", child), errorID).withTraits(NDArray)
    r += node("NDArrayConcat", ("nds", child), ("axis", att("Int"))).withTraits(NDArray)
    r += node("NDArrayRef", ("nd", child), ("idxs", child.*), errorID)
    r += node("NDArraySlice", ("nd", child), ("slices", child)).withTraits(NDArray)
    r += node("NDArrayFilter", ("nd", child), ("keep", child.*)).withTraits(NDArray)
    r += node("NDArrayMap", ("nd", child), ("valueName", name), ("body", child)).withTraits(NDArray)
    r += node(
      "NDArrayMap2",
      ("l", child),
      ("r", child),
      ("lName", name),
      ("rName", name),
      ("body", child),
      errorID,
    )
      .withTraits(NDArray)
    r += node("NDArrayReindex", ("nd", child), ("indexExpr", att("IndexedSeq[Int]")))
      .withTraits(NDArray)
    r += node("NDArrayAgg", ("nd", child), ("axes", att("IndexedSeq[Int]")))
    r += node("NDArrayWrite", ("nd", child), ("path", child)).typed("TVoid.type")
    r += node("NDArrayMatMul", ("l", child), ("r", child), errorID).withTraits(NDArray)
    r += node("NDArrayQR", ("nd", child), ("mode", att("String")), errorID).withCompanionExtension
    r += node(
      "NDArraySVD",
      ("nd", child),
      ("fullMatrices", att("Boolean")),
      ("computeUV", att("Boolean")),
      errorID,
    )
      .withCompanionExtension
    r += node("NDArrayEigh", ("nd", child), ("eigvalsOnly", att("Boolean")), errorID)
      .withCompanionExtension
    r += node("NDArrayInv", ("nd", child), errorID).withTraits(NDArray).withCompanionExtension

    val isScan = ("isScan", att("Boolean"))

    r += node("AggFilter", ("cond", child), ("aggIR", child), isScan)
    r += node("AggExplode", ("array", child), name, ("aggBody", child), isScan)
    r += node("AggGroupBy", ("key", child), ("aggIR", child), isScan)
    r += node(
      "AggArrayPerElement",
      ("a", child),
      ("elementName", name),
      ("indexName", name),
      ("aggBody", child),
      ("knownLength", child.?),
      isScan,
    )
    r += node(
      "AggFold",
      ("zero", child),
      ("seqOp", child),
      ("combOp", child),
      ("accumName", name),
      ("otherAccumName", name),
      isScan,
    )
      .withCompanionExtension

    r += node(
      "ApplyAggOp",
      ("initOpArgs", child.*),
      ("seqOpArgs", child.*),
      ("aggSig", att("AggSignature")),
    )
      .withClassExtension.withCompanionExtension
    r += node(
      "ApplyScanOp",
      ("initOpArgs", child.*),
      ("seqOpArgs", child.*),
      ("aggSig", att("AggSignature")),
    )
      .withClassExtension.withCompanionExtension
    r += node("InitOp", ("i", att("Int")), ("args", child.*), ("aggSig", att("PhysicalAggSig")))
    r += node("SeqOp", ("i", att("Int")), ("args", child.*), ("aggSig", att("PhysicalAggSig")))
    r += node("CombOp", ("i1", att("Int")), ("i2", att("Int")), ("aggSig", att("PhysicalAggSig")))
    r += node("ResultOp", ("idx", att("Int")), ("aggSig", att("PhysicalAggSig")))
      .withCompanionExtension
    r += node("CombOpValue", ("i", att("Int")), ("value", child), ("aggSig", att("PhysicalAggSig")))
    r += node("AggStateValue", ("i", att("Int")), ("aggSig", att("AggStateSig")))
    r += node(
      "InitFromSerializedValue",
      ("i", att("Int")),
      ("value", child),
      ("aggSig", att("AggStateSig")),
    )
    r += node(
      "SerializeAggs",
      ("startIdx", att("Int")),
      ("serializedIdx", att("Int")),
      ("spec", att("BufferSpec")),
      ("aggSigs", att("IndexedSeq[AggStateSig]")),
    )
    r += node(
      "DeserializeAggs",
      ("startIdx", att("Int")),
      ("serializedIdx", att("Int")),
      ("spec", att("BufferSpec")),
      ("aggSigs", att("IndexedSeq[AggStateSig]")),
    )
    r += node(
      "RunAgg",
      ("body", child),
      ("result", child),
      ("signature", att("IndexedSeq[AggStateSig]")),
    )
    r += node(
      "RunAggScan",
      ("array", child),
      name,
      ("init", child),
      ("seqs", child),
      ("result", child),
      ("signature", att("IndexedSeq[AggStateSig]")),
    )

    r += node("MakeStruct", ("fields", tup(att("String"), child).*)).typed("TStruct")
    r += node("SelectFields", ("old", child), ("fields", att("IndexedSeq[String]")))
      .typed("TStruct")
    r += node(
      "InsertFields",
      ("old", child),
      ("fields", tup(att("String"), child).*),
      ("fieldOrder", att("Option[IndexedSeq[String]]")).withDefault("None"),
    )
      .typed("TStruct")
    r += node("GetField", ("o", child), ("name", att("String")))
    r += node("MakeTuple", ("fields", tup(att("Int"), child).*))
      .typed("TTuple").withCompanionExtension
    r += node("GetTupleElement", ("o", child), ("idx", att("Int")))

    r += node("In", ("i", att("Int")), ("_typ", att("EmitParamType")))
      .withDocstring("Function input").withCompanionExtension

    r += node("Die", ("message", child), ("_typ", att("Type")), errorID).withCompanionExtension
    r += node("Trap", ("child", child)).withDocstring(
      """The Trap node runs the `child` node with an exception handler. If the child throws a
        |HailException (user exception), then we return the tuple ((msg, errorId), NA). If the child
        |throws any other exception, we raise that exception. If the child does not throw, then we
        |return the tuple (NA, child value).
        |""".stripMargin
    )
    r += node("ConsoleLog", ("message", child), ("result", child))

    r += node(
      "ApplyIR",
      ("function", att("String")),
      ("typeArgs", att("Seq[Type]")),
      ("args", child.*),
      ("returnType", att("Type")),
      errorID,
    )
      .withMethod(
        """var conversion: (Seq[Type], IndexedSeq[IR], Int) => IR = _
          |var inline: Boolean = _
          |
          |private lazy val refs = args.map(a => Ref(freshName(), a.typ)).toArray
          |lazy val body: IR = conversion(typeArgs, refs, errorID).deepCopy()
          |lazy val refIdx: Map[Name, Int] = refs.map(_.name).zipWithIndex.toMap
          |
          |lazy val explicitNode: IR = {
          |  val ir = Let(refs.map(_.name).zip(args), body)
          |  assert(ir.typ == returnType)
          |  ir
          |}
          |""".stripMargin
      )

    r += node(
      "Apply",
      ("function", att("String")),
      ("typeArgs", att("Seq[Type]")),
      ("args", child.*),
      ("returnType", att("Type")),
      errorID,
    ).withTraits(Apply())

    r += node(
      "ApplySeeded",
      ("function", att("String")),
      ("_args", child.*),
      ("rngState", child),
      ("staticUID", att("Long")),
      ("returnType", att("Type")),
    ).withTraits(Apply())
      .withMethod("val args = rngState +: _args")
      .withMethod("val typeArgs: Seq[Type] = Seq.empty[Type]")

    r += node(
      "ApplySpecial",
      ("function", att("String")),
      ("typeArgs", att("Seq[Type]")),
      ("args", child.*),
      ("returnType", att("Type")),
      errorID,
    ).withTraits(Apply(missingnessAware = true))

    r += node("LiftMeOut", ("child", child))

    r += node("TableCount", tableChild)
    r += node("MatrixCount", matrixChild)
    r += node("TableAggregate", tableChild, ("query", child))
    r += node("MatrixAggregate", matrixChild, ("query", child))
    r += node("TableWrite", tableChild, ("writer", att("TableWriter")))
    r += node(
      "TableMultiWrite",
      ("_children", tableChild.*),
      ("writer", att("WrappedMatrixNativeMultiWriter")),
    )
    r += node("TableGetGlobals", tableChild)
    r += node("TableCollect", tableChild)
    r += node("MatrixWrite", matrixChild, ("writer", att("MatrixWriter")))
    r += node(
      "MatrixMultiWrite",
      ("_children", matrixChild.*),
      ("writer", att("MatrixNativeMultiWriter")),
    )
    r += node("TableToValueApply", tableChild, ("function", att("TableToValueFunction")))
    r += node("MatrixToValueApply", matrixChild, ("function", att("MatrixToValueFunction")))
    r += node(
      "BlockMatrixToValueApply",
      blockMatrixChild,
      ("function", att("BlockMatrixToValueFunction")),
    )
    r += node("BlockMatrixCollect", blockMatrixChild)
    r += node("BlockMatrixWrite", blockMatrixChild, ("writer", att("BlockMatrixWriter")))
    r += node(
      "BlockMatrixMultiWrite",
      ("blockMatrices", blockMatrixChild.*),
      ("writer", att("BlockMatrixMultiWriter")),
    )

    r += node(
      "CollectDistributedArray",
      ("contexts", child),
      ("globals", child),
      ("cname", name),
      ("gname", name),
      ("body", child),
      ("dynamicID", child),
      ("staticID", att("String")),
      ("tsd", att("Option[TableStageDependency]")).withDefault("None"),
    )

    r += node(
      "ReadPartition",
      ("context", child),
      ("rowType", att("TStruct")),
      ("reader", att("PartitionReader")),
    )
    r += node(
      "WritePartition",
      ("value", child),
      ("writeCtx", child),
      ("writer", att("PartitionWriter")),
    )
    r += node("WriteMetadata", ("writeAnnotations", child), ("writer", att("MetadataWriter")))
    r += node(
      "ReadValue",
      ("path", child),
      ("reader", att("ValueReader")),
      ("requestedType", att("Type")),
    )
    r += node(
      "WriteValue",
      ("value", child),
      ("path", child),
      ("writer", att("ValueWriter")),
      ("stagingFile", att("Option[IR]")).withDefault("None"),
    )

    r.result()
  }

  @main
  def main(path: String) = {
    val pack = "package is.hail.expr.ir.defs"
    val imports = Seq(
      "is.hail.annotations.Annotation",
      "is.hail.io.{AbstractTypedCodecSpec, BufferSpec}",
      "is.hail.types.virtual.{Type, TArray, TStream, TVoid, TStruct, TTuple}",
      "is.hail.utils.{FastSeq, StringEscapeUtils}",
      "is.hail.expr.ir.{BaseIR, IR, TableIR, MatrixIR, BlockMatrixIR, Name, UnaryOp, BinaryOp, " +
        "ComparisonOp, CanEmit, AggSignature, EmitParamType, freshName, TableWriter, " +
        "WrappedMatrixNativeMultiWriter, MatrixWriter, MatrixNativeMultiWriter, BlockMatrixWriter, " +
        "BlockMatrixMultiWriter, ValueReader, ValueWriter}",
      "is.hail.expr.ir.lowering.TableStageDependency",
      "is.hail.expr.ir.agg.{PhysicalAggSig, AggStateSig}",
      "is.hail.expr.ir.functions.{UnseededMissingnessAwareJVMFunction, " +
        "UnseededMissingnessObliviousJVMFunction, TableToValueFunction, MatrixToValueFunction, " +
        "BlockMatrixToValueFunction}",
      "is.hail.expr.ir.defs.exts._",
      "scala.language.implicitConversions",
    )
    val gen = pack + "\n\n" + imports.map(i => s"import $i").mkString("\n") + "\n\n" + allNodes.map(
      _.generateDef
    ).mkString("\n")
    os.write(os.Path(path) / "IR_gen.scala", gen)
  }

  def main(args: Array[String]): Unit = ParserForMethods(this).runOrExit(args)
}
