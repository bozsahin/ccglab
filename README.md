# ccglab
Combinatory Categorial Grammar (CCG): All combinators,  parsing to logical form and parameter estimation for CCG and probabilistic CCG.

<b>There is an installer for ccglab, which I describe toward the bottom of README.
           
Please read the preliminaries first to make it ready.</b>
           
This is Common Lisp code running on linux/macos. If you already have an ANSI Common Lisp, it can work with it too.

(GCL and CLisp are ANSI but the first one does not come with CLOS, and CLisp has weird locks on standard package files to turn them on. This is unfortunate because some dispatch macros
for the Lisp reader needs methods, therefore not usable in GCL/Clisp out of the box.)

SBCL and CCL are usable out of the box for CCGlab. 

I added Allegro CL support for CCGlab, but somewhat reluctantly. Its free versions are so cryptic about heap control
you will spend most of your time garbage-collecting rather tha doing useful work. Not worth it, folks.

Design and development of CCGlab continues to be in SBCL, then checked with CCL. Fingers crossed for Allegro CL.

<b>PRELIMINARIES FOR WINDOWS</b>

You need a linux/unix system for CCGlab, either real or in a virtual box such as Oracle's: https://www.virtualbox.org/.

A virtual box can be installed in Windows, which effectively gives CCGlab in Windows.

Then follow one of the advices below for linuxes, depending on your (virtual) machine.

I recommend setting up an Ubuntu virtualbox, because it allows you to try without fully installing it.

If you use CCGLAB from a virtualbox, save your machine state rather than power off the virtual machine.
You won't have to do all of the above over and over.

Even better, put a linux partition on your machine if you intend to use CCGlab quite often. You might forget
to save the machine state one day, and you'd have to start all over again.

<b>PRELIMINARIES for LINUX/MACOS USERS</b>

You need
<ol>
<li> git
<li> wget
<li> an installer (apt-get, yum, or brew, depending on your architecture)
</ol>

The installers have quirky options for finding packages that CCGlab needs.
Do the following to get the preliminaries out of the way properly:

<em>MACOS</em>

<ol>
<li> Open the <code>terminal</code> app.
<li> get brew by executing these from the command line:
           <br> <code>/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"</code>
<li> <code>brew install git</code>
<li> <code>brew install wget</code>
</ol>


<em>UBUNTU/DEBIAN/MINT</em>

<ol>
<li> <code>sudo add-apt-repository universe</code>

<li> <code>sudo apt-get update</code>

<li> <code>sudo apt-get install git</code>

<li> <code>sudo apt-get install wget</code>
</ol>


<em>FEDORA/RedHat</em>


<ol>
<li> <code>sudo yum install yum-utils</code>
<li> <code>sudo yum-config-manager --enable \*</code>
<li> <code>sudo yum install git</code>
<li> <code>sudo yum install wget</code>
</ol>

<em>OTHER LINUXES</em>

Arch, Suse, MacOS do not seem to have this peculiar Ubuntu and RedHat/Fedora caste of packages. 

The packages for sbcl and rlwrap are available for them. CCL Lisp too, if you feel like using it instead of SBCL.

<B>FIRST TIME INSTALL of CCGLAB</B>

<ol>
<li> <code>cd h</code>, where <code>h</code> is your chosen parent directory for CCGlab.
<li> <code>git clone https://github.com/bozsahin/ccglab</code>
<br>This will create the repository in <code>h/ccglab</code>
<br>This is your ccglab home.
<li> <code>cd ccglab</code>
<li> Execute <code>./run-to-complete-first-time-install</code> bash script in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account. <br>
<li> Open a new bash terminal and run <code>ccglab</code> script from anywhere.
</ol>

<b>NO REINSTALL:</b> If you already have a git-installed up-and-running CCGlab, just do the following for updates:

<ol>
<li><code>cd $CCGLAB_HOME</code>
<li><code>git pull</code>
</ol>

Latest release is shown by <code>(which-ccglab).</code> Announced git releases may be slightly behind the latest,
which is always this copy. Just clone this repo rather than download the release if you want the latest.

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

The installer fetches the relevant sources (lalrparser, sbcl, rlwrap) and does the manual install automatically, and saves it in the files <code>.bash_profile, .bashrc</code> at your home.

<b>Have a look at the companion repos, <a href="https://github.com/bozsahin/ccglab-grammars">ccglab-grammars</a>, 
and <a href="https://github.com/bozsahin/ccglab-models">ccglab-models</a>, which contain grammars and models developed in CCGlab</b>.

<b>TO DO:</b> 
<ul>
<li> bidirectional unary rules.
<li> web server, for use without install.
</ul>

enjoy.--Cem Bozsahin
