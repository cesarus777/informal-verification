#pragma once

#include <atomic>
#include <concepts>
#include <memory>
#include <ostream>
#include <stdexcept>

template <typename T> class LockFreeStack final {
private:
  std::ostream &OS;

  struct Node {
    template <class... ArgsTys>
    Node(ArgsTys &&...Args)
        : Data(std::make_shared<T>(std::forward<ArgsTys>(Args)...)) {}

    std::shared_ptr<T> Data;
    Node *Next = nullptr;
  };

  std::atomic<Node *> ToBeDeleted = nullptr;
  std::atomic<unsigned> ThreadsInPop = 0;
  std::atomic<Node *> Head = nullptr;

public:
  LockFreeStack(std::ostream &OS) : OS(OS) {}
  LockFreeStack(const LockFreeStack &) = delete;
  LockFreeStack(LockFreeStack &&) = delete;
  LockFreeStack &operator=(const LockFreeStack &) = delete;
  LockFreeStack &operator=(LockFreeStack &&) = delete;
#if 0
  ~LockFreeStack() noexcept(false) {
    if (ToBeDeleted.load()) {
      OS << '\n';
      deleteNodes(ToBeDeleted);
      throw std::runtime_error{
          "LockFreeStack: not all stack elements were deleted"};
    }

    if (!isEmpty()) {
      throw std::runtime_error{
          "LockFreeStack: not all stack elements were popped"};
    }
  }
#endif

  void push(const T &Data)
    requires(std::copy_constructible<T>)
  {
    OS << '0';
    Node *const NewNode = new Node(Data);
    NewNode->Next = Head.load();
    while (!Head.compare_exchange_weak(NewNode->Next, NewNode))
      ;
  }

  void push(T &&Data)
    requires(std::move_constructible<T>)
  {
    OS << '0';
    Node *const NewNode = new Node(std::move(Data));
    NewNode->Next = Head.load();
    while (!Head.compare_exchange_weak(NewNode->Next, NewNode))
      ;
  }

  std::shared_ptr<T> pop() {
    OS << '1';
    ++ThreadsInPop;
    Node *OldHead = Head.load();
    while (OldHead && !Head.compare_exchange_weak(OldHead, OldHead->Next))
      ;

    std::shared_ptr<T> Res;
    if (OldHead) {
      Res.swap(OldHead->Data);
    }
    tryReclaim(OldHead);
    return Res;
  }

  bool isEmpty() { return Head == nullptr; }

private:
  static void deleteNodes(Node *Nodes) {
    while (Nodes) {
      Node *Next = Nodes->Next;
      delete Nodes;
      Nodes = Next;
    }
  }

  void tryReclaim(Node *OldHead) {
    if (ThreadsInPop == 1) {
      Node *NodesToDelete = ToBeDeleted.exchange(nullptr);
      if (!--ThreadsInPop) {
        deleteNodes(NodesToDelete);
      } else if (NodesToDelete) {
        chainPendingNodes(NodesToDelete);
      }
      delete OldHead;
    } else {
      chainPendingNode(OldHead);
      --ThreadsInPop;
    }
  }

  void chainPendingNodes(Node *Nodes) {
    Node *Last = Nodes;
    while (Node *const Next = Last->Next) {
      Last = Next;
    }
    chainPendingNodes(Nodes, Last);
  }

  void chainPendingNodes(Node *First, Node *Last) {
    Last->Next = ToBeDeleted;
    while (!ToBeDeleted.compare_exchange_weak(Last->Next, First))
      ;
  }

  void chainPendingNode(Node *N) { chainPendingNodes(N, N); }
};
