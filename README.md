# ccglab
Combinatory Categorial Grammar (CCG): All combinators, common grammar format, parsing to logical form (aka semantic parsing), parameter estimation for probabilistic CCG.

<b>Have a look at the companion repos, <a href="https://github.com/bozsahin/ccglab-grammars">ccglab-grammars</a>, 
and <a href="https://github.com/bozsahin/ccglab-models">ccglab-models</a>, which contain grammars and models developed in CCGlab</b>.

This is Common Lisp code running on linux/macos. If you already have an ANSI Common Lisp, it can work with it too.

(GCL is ANSI but it does not come with CLOS. This is unfortunate because some dispatch macros
for the Lisp reader needs methods, therefore not usable in GCL out of the box.)

SBCL and CCL are usable out of the box for CCGlab. 

<b>PRELIMINARIES for LINUX/MACOS USERS</b>

You need
<ol>
<li> git
<li> wget
<li> an installer (apt-get, yum, or brew, depending on your architecture)
</ol>

The installers have quirky options for finding packages that CCGlab needs.

Before you run the CCGlab installer, do the following:

<em>UBUNTU/DEBIAN/MINT</em>

<ol>
<li> <code> sudo add-apt-repository universe</code>

<li> <code>sudo apt-get update</code>

<li> <code>apt-get install git</code>

<li> <code>apt-get install wget</code>
</ol>

If you're not the machine's administrator, you need <code>sudo</code> priviledges to do 3-4.

<em>FEDORA/RedHat</em>

<ol>
<li> <code>yum-config-manager --enable \\*</code>
<li> <code> yum install git</code>
<li> <code> yum install wget</code>
</ol>

If you're not the machine's administrator, you need <code>sudo</code> priviledges to do 2-3.

<em>OTHER LINUXES</em>

Arch, Suse, MacOS do not seem to have this peculiar Ubuntu and RedHat/Fedora caste of packages. 

The packages for sbcl and rlwrap are available for them. CCL Lisp too; if you feel like using it instead of SBCL.

<b>PRELIMINARIES FOR WINDOWS</b>

You need a linux/unix system, either real or in a virtual box such as Oracle's: https://www.virtualbox.org/.

A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.

Then follow some of the advice above for linuxes, depending on your virtual machine.

I recommend seting up an Ubuntu virtualbox, because it allows you to try it without fully installing it.

If you use CCGLAB from a virtualbox, save your machine state rather than power off the virtual machine.
You won't have to do all of the above over and over.

<B>FIRST TIME INSTALL</B>

<ol>
<li> <code>cd h</code>, where <code>h</code> is your chosen parent directory for CCGlab.
<li> <code>git clone https://github.com/bozsahin/ccglab</code>
<br>This will create the repository in <code>h/ccglab</code>
<br>This is your ccglab home.
<li> <code>cd h/ccglab</code>
<li> Execute <code>./run-to-complete-first-time-install</code> bash script in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account. <br>
<li> Open a new bash terminal and run <code>ccglab</code> script from anywhere.
</ol>

<b>NO NEED TO REINSTALL:</b> If you already have a git-installed up-and-running CCGlab, just do the following for updates:

<ol>
<li><code>cd $CCGLAB_HOME</code>
<li><code>git pull</code>
</ol>

Latest release is shown by <code>(which-ccglab).</code> Announced git releases may be slightly behind the latest,
which is always this copy. Just clone this rather than download the release if you want the latest.

<B>MANUAL INSTALL:</B>

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
