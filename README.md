# ccglab
Combinatory Categorial Grammar (CCG): All combinators, native input format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

This branch is for gitters. Choose a directory, then clone this branch only, as shown below, and run the <code>run-to-complete-ccglab-install</code> in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account.

<code>git clone -b git-install --single-branch git://github.com/bozsahin/ccglab.git</code>

This is Common Lisp code. If you already have an ANSI Common Lisp, it can work with it too.

Current version is 3.1, use (which-ccglab) in your system to find out whether you've got the latest.

SOFTWARE REQUIREMENTS:

You need a linux/unix system, either real or in a virtual box such as Oracle's: https://www.virtualbox.org/.

If you want the installer to install a Common Lisp and <code>rlwrap</code> for you, you need either
<ul>
<li> <code>apt-get</code> (the most common package installer for linuxes).
<li> <code>brew</code> https://brew.sh/ (a common installer for MacOS)
</ul>

A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.

Linuxes and MacOSs are native environments for CCGlab.

That will give you what CCGlab needs for fully automatic install and run:

<code>bash, sed, apt-get/brew, wget, sudo </code>(you need the last one only if you want the installer to install SBCL Lisp and <code>rlwrap</code> for you--highly recommended)

With the exception of <code>apt-get/brew</code> the rest is available out-of-the-box in most if not all linuxes. 
To make sure, do e.g. <code>which apt-get</code> to find out. If you don't get a response, you don't have it.

NO NEED FOR REINSTALL: If you already have a git-installed CCGlab, just do the following for updates:

<code>cd $CCGLAB_HOME</code>
<code>git pull</code>

enjoy.
--Cem Bozsahin
