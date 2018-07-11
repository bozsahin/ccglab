# ccglab
Combinatory Categorial Grammar (CCG): All combinators, native input format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

<b>Have a look at the companion repos, <a href="https://github.com/bozsahin/ccglab-grammars">ccglab-grammars</a>, 
and <a href="https://github.com/bozsahin/ccglab-models">ccglab-models</a>, which contain grammars and models developed in CCGlab</b>.

<em>FIRST TIME INSTALL (assuming you have <code>git</code>):</em>

<ol>
<li> <code>cd h</code>, where <code>h</code> is your chosen parent directory for CCGlab.
<li> <code>git clone git://github.com/bozsahin/ccglab</code>
<br>This will create the repository in <code>h/ccglab</code>
<br>This is your ccglab home.
<li> <code>cd h/ccglab</code>
<li> Execute <code>./run-to-complete-first-time-install</code> bash script in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account. <br>
<b>Please read the rest of this document before you run the script.</b>
<li> Open a new bash terminal and run <code>ccglab</code> script from anywhere.
</ol>

<b>NO NEED TO REINSTALL:</b> If you already have a git-installed up-and-running CCGlab, just do the following for updates:

<ol>
<li><code>cd $CCGLAB_HOME</code>
<li><code>git pull</code>
</ol>

This is Common Lisp code. If you already have an ANSI Common Lisp, it can work with it too.

(GCL is ANSI but it does not come with CLOS. This is unfortunate because some dispatch macros
for the Lisp reader needs methods, therefore not usable in GCL out of the box.)

SBCL and CCL are usable out of the box for CCGlab.

Latest release is shown by <code>(which-ccglab).</code> Announced git releases may be slightly behind the latest,
which is always this copy. Just clone this rather than download the release if you want the latest.

<em>SOFTWARE REQUIREMENTS:</em>

You need a linux/unix system, either real or in a virtual box such as Oracle's: https://www.virtualbox.org/.

If you want the installer to install a Common Lisp and <code>rlwrap</code> for you, you need either
<ul>
<li> <code>apt-get</code> (the most common package installer for linuxes, at least for debian-based linuxes--ubuntu, linux mint, debian etc.).
<li> <code>brew</code> https://brew.sh/ (a common installer for MacOS)
           <li> <code>yum</code> (installer for redhat spin offs including Fedora)
</ul>

If you have all of them, like me, it installs with <code>brew</code>.

A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.

Linuxes and MacOSs are native environments for CCGlab.

<b> You need the following to run the install script</b>:

<code>apt-get/brew/yum, wget</code>

To make sure, do e.g. <code>which wget</code> to find out. If you don't get a response, you don't have it.

<em>NEW TO UBUNTU?</em>

Ubuntu has built-in packages for SBCL and rlwrap, which <code>apt-get</code> in the ccglab install script
can install very easily. 

It's just that Ubuntu starts with non-basic packages turned off so it can't seem to find SBCL/rlwrap
in the beginning. Do the following to enable them before running
the ccglab install completion script.

           sudo add-apt-repository universe
           sudo apt-get update

<em>ARE YOU FEDORAized?</em>

Like Ubuntu's apt-get, Fedora installer is weird; it's repos are all closed by default, so the installer won't work out of the box. 
Find out where
<code>sbcl</code> and <code>rlwrap</code> are in the yum-world.

<em>OTHER LINUXES</em>

Arch, Mint, Suse, Debian, MacOS do not seem to have this peculiar Ubuntu and RedHat caste of packages. 

The packages for sbcl and rlwrap are available for them. CCL too.

<em>MANUAL INSTALL:</em>

The installer script works for several linuxes and unixes and their derivatives (Ubuntu, Debian, Mint, Fedora, Redhat, MacOS).

If you're tired of weird defaults of linux installers, try the safe and longer way:

<ul>
<li> If you use Windows, install virtualbox, set an Ubuntu or Mint machine (easiest ones), and follow the instructions above for install.
<li> If you have another linux (arch, debian suse etc.), just clone this repo, get <a href="http://web.science.mq.edu.au/~mjohnson/code/lalrparser.lisp">lalr</a>
somewhere in your machine, and set and <code>export</code> the following bash variables:
<ol>
<li><code>CCGLAB_HOME</code> to where the <code>ccglab</code> repo is
<li><code>LALR_HOME</code> to where you saved lalrparser.lisp
<li><code>CCGLAB_LISP</code> to full path of your ANSI Common Lisp binary
<li><code>RLWRAP</code> to path of <code>rlwrap</code> if you have it, otherwise nil, i.e. <code>RLWRAP=</code>
<li><code>PATH=:.:$CCGLAB_HOME/bin:$PATH</code> to overrride earlier installs of ccglab.
<li> Then open a new <code>bash</code> terminal and run <code>ccglab</code>
</ol>
</ul>

Here is my local setup in <code>~/.bashrc</code> file (create one if you don't have it):

           export CCGLAB_HOME=$HOME/mysrc/myrepos/ccglab
           export LALR_HOME=$HOME/mysrc/lisp
           export CCGLAB_LISP=/usr/local/bin/sbcl
           export RLWRAP=rlwrap
           export PATH=:.:$CCGLAB_HOME/bin:$PATH 
           
And here is my <code>~/.bash_profile</code> file (create one if you don't have it---bash may or may not use both):

           if [ -f ~/.bashrc ]; then
                      source ~/.bashrc
           fi

The installer does all that and more, from fetching lalrparser.lisp to setting variables, paths and bash files and installing
SBCL and rlwrap.

enjoy.--Cem Bozsahin
