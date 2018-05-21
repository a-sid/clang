// RUN: %clang_analyze_cc1 -analyzer-checker=alpha.test.MatcherRetain %s -verify

struct Counter {
  void startCounting();
  void retain();
  void release();
};

Counter obj;

void testSingleRetain() {
  obj.startCounting();
  obj.retain(); // no-warning
}

void test2Retains3Releases() {
  obj.startCounting();
  obj.retain();
  obj.retain();
  obj.release();
  obj.release();
  obj.release();  // expected-warning{{}}
}

void test14Retains14Releases(void) {
  obj.startCounting();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release(); // no-warning
}

void test14Retains15Releases(void) {
  obj.startCounting();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.retain();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release();
  obj.release(); // expected-warning{{}}
}
