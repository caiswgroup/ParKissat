SRCS = $(shell find . -name "*.cpp")

OBJS = $(addsuffix .o, $(basename $(SRCS)))

EXEC = painless

LIBS = -lm4ri -L../m4ri-20140914/.libs \
       -lkissat -L../kissat_bonus/build \
       -lpthread -lz -lm -static

CXXFLAGS = -I../m4ri-20140914 \
           -I. \
           -I../kissat_bonus \
           -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS \
           -fopenmp -std=c++17 -O3 -g -D NDEBUG

$(EXEC): $(OBJS)
	$(CXX) -o $@ $^ $(CXXFLAGS) $(LIBS)

%.o: %.cpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) $(LIBS)

clean:
	rm -f $(OBJS) $(EXEC)
