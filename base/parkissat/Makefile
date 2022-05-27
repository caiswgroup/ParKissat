all:
	##################################################
	###   			     m4ri                     ###
	##################################################
	# Note that we only use some basic package of Maple to implement FME and GE.
	##################################################
	tar zxvf m4ri-20140914.tar.gz && \
	cd m4ri-20140914 && ./configure;
	+ $(MAKE) -C m4ri-20140914

	##################################################
	###               kissat_bound                 ###
	##################################################
	chmod a+x kissat_bonus/configure kissat_bonus/scripts/*.sh
	cd kissat_bonus && ./configure --compact
	+ $(MAKE) -C kissat_bonus

	##################################################
	###                 PaInleSS                   ###
	##################################################
	+ $(MAKE) -C painless-src
	mv painless-src/painless parkissat

clean:
	##################################################
	###                 PaInleSS                   ###
	##################################################
	rm -rf m4ri-20140914
	+ $(MAKE) clean -C painless-src
	+ $(MAKE) clean -C kissat_bonus
	rm -f parkissat
