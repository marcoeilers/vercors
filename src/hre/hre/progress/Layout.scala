package hre.progress


case object Layout {
  var forceProgress: Boolean = false


  def install(progress: Boolean): Unit = {
    forceProgress = progress
  }





  def maxWidth: Int = 78

  def maxHeight: Int = 32

  private def esc(command: Char, args: String = ""): String =
    "\u001b[" + args + command

  private def upBy(n: Int): String = if(n==0) "" else esc('A', n.toString)

  private def clearLine: String = esc('K')
  private def clearToEnd: String = esc('J', "0")

  private var printedLines = 0

  def undoProgressMessage: String =
     ""

  def progressEstimate: Double = TaskRegistry.getRootTask.progress

  def progressBadge: String =
    f"[${progressEstimate * 100}%.1f%%]"

  def progressBar: String = {
    ""
  }

  def progressMessage: String = ""

  private var currentProgressMessage = ""

  /**
   * Print an updated progress message to stdout
   * @return whether the number of printed progres lines changed
   */
  def update(): Boolean = {
    false
  }

  def withProgressDiscarded(out: String): String =
    undoProgressMessage + out + currentProgressMessage
}
