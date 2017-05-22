# ccglab
Combinatory Categorial Grammar (CCG): All combinators, native input format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

This branch is for gitters. Choose a directory, then clone this branch only as below, and run the <code>run-to-complete-ccglab-install</code> to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account.

<code>git clone -b git-install --single-branch git://github.com/bozsahin/ccglab.git</code>

You need to be able to <code>sudo</code> on your machine if you want the installer to install Lisp and rlwrap for you.

This is Common Lisp code. If you already have an ANSI Common Lisp, it can work with it too.

Current version is 3.1, use (which-ccglab) in your system to find out whether you've got the latest.

SOFTWARE REQUIREMENTS:

You need a linux/unix system, either real or in a virtual box such as Oracle's.
A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.
Linuxes and MacOSs are native environments for CCGlab.
You might need to install brew in a Mac.

That will give you what CCGlab needs for fully automatic install:

bash (shell for linux)

sed (stream editor)

apt-get or brew (installers for linux or MacOS systems)

wget (downloader)

sudo (if you want the installer to install SBCL and rlwrap for you--recommended)

With the exception of apt-get/brew the rest is already available in most if not all linuxes. 
To make sure, do e.g. 'which apt-get' to find out.

--Cem Bozsahin
