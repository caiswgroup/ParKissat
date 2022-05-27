all:
	$(MAKE) -C "/root/zxd/solvers/kissat/build"
kissat:
	$(MAKE) -C "/root/zxd/solvers/kissat/build" kissat
tissat:
	$(MAKE) -C "/root/zxd/solvers/kissat/build" tissat
clean:
	rm -f "/root/zxd/solvers/kissat"/makefile
	-$(MAKE) -C "/root/zxd/solvers/kissat/build" clean
	rm -rf "/root/zxd/solvers/kissat/build"
coverage:
	$(MAKE) -C "/root/zxd/solvers/kissat/build" coverage
indent:
	$(MAKE) -C "/root/zxd/solvers/kissat/build" indent
test:
	$(MAKE) -C "/root/zxd/solvers/kissat/build" test
.PHONY: all clean coverage indent kissat test tissat
