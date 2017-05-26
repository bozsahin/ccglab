# ccglab
Combinatory Categorial Grammar (CCG): All combinators, native input format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

This branch is for gitters. FOR FIRST TIME INSTALL:

<ol>
<li> <code>cd h</code>, where <code>h</code> is your chosen home for CCGlab.
<li> <code>git clone -b git-install --single-branch git://github.com/bozsahin/ccglab</code>
<br>This will create the repo in <code>h/ccglab</code>
<li> <code>cd h/ccglab</code>
<li> <code>run-to-complete-ccglab-install</code> in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account.
<li> Open a new bash terminal and run <code>ccglab</code> script from anywhere.
</ol>

Please read the rest of this document before you run the script.

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

<em>NO NEED TO REINSTALL:</em> If you already have a git-installed up-and-running CCGlab, just do the following for updates:

<ol>
<li><code>cd $CCGLAB_HOME</code>
<li><code>git pull</code>
</ol>

<em>Other linuxes and install:</em>

<ul>
<li> The installer script works for Debian-based linuxes (ubuntu, debian etc.) and MacOS.
<li> If you use Windows, install virtualbox, set an Ubuntu machine (easiest one) and follow the instructions above for install.
<li> If you have another linux, just clone this repo, get <a href="http://web.science.mq.edu.au/~mjohnson/code/lalrparser.lisp">lalr</a>
somewhere in your machine, and set and <code>export</code> the bash variables 
<ol>
<li><code>CCGLAB_HOME</code> to where the <code>ccglab</code> repo is
<li><code>LALR_HOME</code> to where you saved lalrparser.lisp
<li><code>CCGLAB_LISP</code> to full path of your ANSI Common Lisp binary
<li><code>RLWRAP</code> to path of <code>rlwrap</code> if you have it, otherwise nil, i.e. <code>RLWRAP=</code>
<li><code>PATH=$CCGLAB_HOME/bin:$PATH</code> to overrride earlier installs of ccglab.
<li> Then open a new <code>bash</code> terminal and run <code>ccglab</code>
</ol>
</ul>

enjoy.--Cem Bozsahin
