/*
This is a separate file, because targets are generally invalidated if the build definition changes. The fetching target
being in a different file reduces that chance.
*/

import $file.git

import mill._
import git.GitModule

object silverGit extends
  GitModule {
  def url = T { "https://github.com/viperproject/silver.git" }
  def commitish = T { "d6161459c32f58c47c162a467ea675fdfac8fd17" }
}

object siliconGit extends GitModule {
  def url = T { "https://github.com/viperproject/silicon.git" }
  def commitish = T { "57da779a839177ad0c79b7a32cc3d56c38253697" }
}

object carbonGit extends GitModule {
  def url = T { "https://github.com/viperproject/carbon.git" }
  def commitish = T { "e78947392eaf2bcc565a92d1bf7928b2baaf3a51" }
}