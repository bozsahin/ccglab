# ccglab
Combinatory Categorial Grammar (CCG): CCG and probabilistic CCG, with all combinators and their powers.

Install instructions are in this README, <a href="#install">here</a>. There are certain things you need to do depending
on your OS, so please follow the install AFTER reading this README.

           
<code>CCGlab</code> is Common Lisp code with some <code>bash</code> string processing. 

It needs a linux, a native one or one in macosphere or windowsphere. As hard as it is to believe, windowsphere is becoming easier and more native-like (thanks Tim!).

SBCL and CCL Common Lisps are usable out of the box for CCGlab. The <code>install</code> script sets up SBCL for CCGlab if you haven't got one already. If you have an ANSI Common Lisp, it can work with it too.

GCL and CLisp are ANSI but the first one does not come with CLOS, and CLisp has weird locks on standard package files to turn them on. This is unfortunate because some CCGlab macros
for the Lisp reader needs methods, therefore not usable in GCL/Clisp out of the box.

I added Allegro CL support for CCGlab (for calling bash scripts etc.), but somewhat reluctantly. Its free versions are so cryptic about heap control 
you will avoid it, and spend most of your time garbage-collecting rather than doing useful work. Not worth it, folks.

Design and development of CCGlab continues to be in SBCL, then checked with CCL. 

<b>FOR WINDOWS</b>

You need a linux system for CCGlab. There are three options for windows (I recommend the first one):

<ol>
           <li> For windows 10: Follow these <a href="docs/windows10-directions.md">directions</a>. No partitions, no virtualbox, no hassles. You now have linux as a W10 app with ccglab in it.
<li> For windows earlier than W10: install a virtual box such as Oracle's: https://www.virtualbox.org/.

Then follow one of the advices below for linuxes for ccglab install, depending on your virtual machine.

I recommend setting up an Ubuntu or Mint virtualbox if you have no prior linux experience.

If you use CCGLAB from a virtualbox, save your machine state rather than power off the virtual machine.
You won't have to do all of the above over and over.

<li>For any windows: put a linux partition in your machine, and follow the instructions below
depending on your linux. This one is for experienced users.
</ol>

<b>Preliminaries for MACOS</b>

<ol>
<li> Open the <code>terminal</code> app.
<li> get brew by executing these from the command line:
           <br> <code>/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"</code>
<li> <code>brew install git</code>
<li> <code>brew install wget</code>
</ol>


<b>Preliminaries for UBUNTU/DEBIAN/MINT</b>

<ol>
<li> <code>sudo apt-get install git</code>

<li> <code>sudo apt-get install wget</code>
</ol>


<b>Preliminaries for FEDORA/RedHat</b>


<ol>
<li> <code>sudo yum install git</code>
<li> <code>sudo yum install wget</code>
</ol>

<b>For other linuxes</b>

Arch and Suse do not seem to have the peculiar Ubuntu and RedHat/Fedora caste of packages,
so everything should be fine to run the CCGlab installer.

<a name="install">
           
<B>INSTALLING CCGLAB</B>

<ol>
<li> <code>cd h</code>, where <code>h</code> is your chosen parent directory for CCGlab.
<li> <code>git clone https://github.com/bozsahin/ccglab</code>
<br>This will create the repository in <code>h/ccglab</code>
<br>This is your ccglab home.
<li> <code>cd ccglab</code>
<li> Execute <code>./install</code> bash script in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account. <br>
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


<li> Just clone this repo, get the <a href="http://web.science.mq.edu.au/~mjohnson/code/lalrparser.lisp">LALR parser</a>
somewhere in your machine, and set and <code>export</code> the following bash variables:
<ol>
<li><code>CCGLAB_HOME</code> to where the <code>ccglab</code> repo is
<li><code>LALR_HOME</code> to where you saved lalrparser.lisp
<li><code>CCGLAB_LISP</code> to full path of your ANSI Common Lisp binary
<li><code>RLWRAP</code> to path of <code>rlwrap</code> if you have it, otherwise nil, i.e. <code>RLWRAP=</code>
<li><code>PATH=:.:$CCGLAB_HOME/bin:$PATH</code> to overrride earlier installs of ccglab.
<li> Then open a new <code>bash</code> terminal and run <code>ccglab</code>
</ol>

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

Also have a look at the companion repo called <a href="https://github.com/bozsahin/ccglab-database">ccglab-database</a>, which contains grammars and models developed in CCGlab

enjoy.--Cem Bozsahin
