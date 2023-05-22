#include "AnthonyWilliamsStack.hpp"

#include <gtest/gtest.h>

#include <cstring>
#include <ranges>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>

using DataT = int;
using StackT = LockFreeStack<DataT>;

int main(int argc, char *argv[]) {
  if (argc != 2) {
    std::cerr << "Usage: tests NTEST" << std::endl;
    return 1;
  }

  std::ostringstream Trace;
  try {
    size_t NRead;
    auto NTests = std::stoi(argv[1], &NRead);
    if (NRead != std::strlen(argv[1]))
      throw std::runtime_error{"NTESTS expected to be int"};
    if (NTests < 2)
      throw std::runtime_error{"NTESTS expected to be > 1"};
    std::vector<std::jthread> Workers;
    StackT Stack{Trace};
    auto PushTask = [&Stack](DataT X) { Stack.push(X); };
    auto PopTask = [&Stack]() { return Stack.pop(); };
    auto PushPopTask = [&](DataT X) {
      PushTask(X);
      return PopTask();
    };

    if (NTests % 2)
      Workers.emplace_back(PushPopTask, --NTests);

    for (auto I :
         std::views::iota(0, NTests - (NTests % 2)) | std::views::reverse) {
      if (I % 2)
        Workers.emplace_back(PushTask, I / 2);
      else
        Workers.emplace_back(PopTask);
    }
  } catch (std::exception &E) {
    std::cerr << "Error: " << E.what() << std::endl;
    return 2;
  } catch (...) {
    std::cerr << "Unknown exception caught in main" << std::endl;
    return 2;
  }

  std::cout << Trace.view().data() << std::endl;
}
