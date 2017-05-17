# ccglab
Combinatory Categorial Grammar (CCG): All combinators, native input format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

All you need is the easy-install.zip. You can get it by download or git clone; it doesn't matter.

Unzip it in a directory. When you run the revealed script you will get CCGlab/ in that directory if it is a fresh install. Otherwise it will ask you how to upgrade an old CCGlab. (You need to be able to <code>sudo</code> on your machine
if you want the installer to install Lisp and rlwrap for you.)

This is Common Lisp code. Easy-installer installs a CL for you (SBCL), and downloads and installs all necesssary files.
If you already have an ANSI Common Lisp, it can work with it too.

(The main reason for not gitting the repo is automatic install gets various software from various sources.)

Current version is 3.1, use (which-ccglab) in your system to find out whether you've got the latest.

SOFTWARE REQUIREMENTS:

You need a linux/unix system, either real or in a virtual box such as Oracle's.
A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.
Linuxes and MacOSs are native environments for CCGlab.
You might need to install brew in a Mac. Others are standard.

That will give you what CCGlab needs for fully automatic install:

bash (shell for linux)

sed (stream editor)

apt-get or brew (installers for linux or MacOS systems)

wget (downloader)

zip (compressor/decompressor)

sudo (if you want the installer to install SBCL and rlwrap for you--recommended)

They come mostly standard in many linuxes. To make sure, do 'which apt-get' etc to find out.
You need them before CCGlab install.

--Cem Bozsahin
