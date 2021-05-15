# ccglab
Combinatory Categorial Grammar (CCG): CCG and probabilistic CCG, with full set of  combinators and their powers.

<code>CCGlab</code> is <code>Common Lisp</code> code with some <code>bash</code> scripts for install and run-time tokenization. 

<code>CCGlab</code> needs a linux, a native one or one in macosphere or windowsphere. 

<b>INSTALL FOR LINUXSPHERE AND MACOSPHERE</b>

<a name="install">
           
<ol>
<li> <code>git clone https://github.com/bozsahin/ccglab</code>
<br>This will create the repository <code>ccglab</code> under you current directory.
<br>This is your ccglab home.
<li> <code>cd ccglab</code>
<li> Execute <code>./install</code> bash script in the repo to get the extras needed, and to set up the paths so that CCGlab is usable from anywhere in your user account. <br>
</ol>

Depending on your package manager, which is assumed to be either <code>dnf, yum, apt-get, pacman, brew</code> (in this pecking order if all are present in your system),
it will fetch (if not already present in your system) <code>sbcl</code> and <code>rlwrap</code>. All linuxsphere (rolling and nonrolling distros, MACOS, Windows's WSL linux distros) have standard packages for these tools. 

You can then run the <code>ccglab</code> script from anywhere after install.

Latest release is shown by <code>(which-ccglab).</code> Announced git releases may be slightly behind the latest,
which is always this copy. Just clone this repo rather than download the release if you want the latest.

<b>INSTALL FOR WINDOWS</b>

You need a linux system for CCGlab. Once you get that, follow the instructions for Linuxsphere for CCGlab install.

There are three options for windows (I recommend the first one):

<ol>
<li> For windows 10 onwards: Follow these <a href="docs/windows10-directions.md">directions</a>. No partitions, no virtualbox, no hassles. You now have linux as a W10 app with ccglab in it.
<li> For windows earlier than W10: install a virtual box such as Oracle's: https://www.virtualbox.org/.

Then follow one of the advices below for linuxes for ccglab install, depending on your virtual machine.

I recommend setting up an Ubuntu or Mint virtualbox if you have no prior linux experience.

If you use CCGLAB from a virtualbox, save your machine state rather than power off the virtual machine.
You won't have to do all of the above over and over.

<li>For any windows: put a linux partition in your machine, and follow the instructions below
depending on your linux. This one is for experienced users. This option is becoming easier too.
</ol>


<B>MANUAL INSTALL</B>

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

<B>COMMON LISPs FOR CCGLAB</B>

SBCL and CCL Common Lisps are usable out of the box for CCGlab. The <code>install</code> script sets up SBCL for CCGlab if you haven't got one already. If you have an ANSI Common Lisp, it can work with it too.

GCL and CLisp are ANSI but the first one does not come with CLOS, and CLisp has weird locks on standard package files to turn them on. This is unfortunate because some CCGlab macros
for the Lisp reader needs methods, therefore not usable in GCL/Clisp out of the box.

I added Allegro CL support for CCGlab (for calling bash scripts etc.), but somewhat reluctantly. Its free versions are so cryptic about heap control 
you will avoid it, and spend most of your time garbage-collecting rather than doing useful work. Not worth it, folks.

Design and development of CCGlab continues to be in SBCL, then occasionally checked with CCL. 

<B>THE WRAPPER</B>

I hope you appreciate the peace and comfort of <code>rlwrap</code> when you use a command-line tool like CCGlab. I am eternally grateful to its developers.


enjoy.

--Cem Bozsahin
