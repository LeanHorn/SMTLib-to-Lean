// Exercise the compiled FFI with counted versions of its external wrappers.
#include <cvc5/cvc5.h>
#include <lean/lean.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>

extern "C" {
void lean_initialize();
uint64_t term_hash(lean_obj_arg);
uint8_t term_beq(lean_obj_arg, lean_obj_arg);
uint64_t sort_hash(lean_obj_arg);
uint8_t sort_beq(lean_obj_arg, lean_obj_arg);
}

template <typename T> struct Counted {
  static inline unsigned created = 0, finalized = 0;
  static void finalize(void* value) {
    ++finalized;
    delete static_cast<T*>(value);
  }
  static void visit(void*, b_lean_obj_arg) {}
  static lean_object* wrap(const T& value) {
    static auto* cls = lean_register_external_class(finalize, visit);
    ++created;
    return lean_alloc_external(cls, new T(value));
  }
};

static void check(bool condition, const char* type, const char* message) {
  if (!condition) {
    std::fprintf(stderr, "%s ownership: %s\n", type, message);
    std::exit(1);
  }
}

template <typename T>
static void exercise(const char* type, const T& seed, const T& other,
                     uint64_t (*hash)(lean_obj_arg),
                     uint8_t (*equal)(lean_obj_arg, lean_obj_arg)) {
  using C = Counted<T>;
  constexpr unsigned iterations = 10000;
  const auto expected_hash = std::hash<T>()(seed);
  for (unsigned i = 0; i < iterations; ++i) {
    check(hash(C::wrap(seed)) == expected_hash, type, "hash result changed");
    check(equal(C::wrap(seed), C::wrap(seed)), type, "equal values differ");
    check(!equal(C::wrap(seed), C::wrap(other)), type, "unequal values match");
    auto* alias = C::wrap(seed);
    lean_inc(alias); // Two owned arguments, even when both point to one wrapper.
    check(equal(alias, alias), type, "self comparison failed");
  }
  check(C::created == C::finalized, type, "fresh wrappers were not released");

  auto* owner = C::wrap(seed);
  for (unsigned i = 0; i < iterations; ++i) {
    lean_inc(owner); // Preserve our owner while transferring one reference.
    check(hash(owner) == expected_hash, type, "retained hash result changed");
    check(owner->m_rc == 1, type, "hash retained an owned reference");
    lean_inc(owner);
    check(!equal(owner, C::wrap(other)), type, "retained unequal values match");
    check(owner->m_rc == 1, type, "equality retained an owned reference");
    lean_inc(owner);
    lean_inc(owner);
    check(equal(owner, owner), type, "retained self comparison failed");
    check(owner->m_rc == 1, type, "self comparison retained an owned reference");
  }
  check(C::created == C::finalized + 1, type, "unexpected retained wrappers");
  lean_dec(owner);
  check(C::created == C::finalized, type, "owner was not finalized");
  std::printf("PASS %s ownership: %u wrappers created and finalized\n", type, C::created);
}

int main() {
  lean_initialize();
  cvc5::TermManager tm;
  exercise("Term", tm.mkInteger(17), tm.mkInteger(18), term_hash, term_beq);
  exercise("Sort", tm.getIntegerSort(), tm.getBooleanSort(), sort_hash, sort_beq);
}
