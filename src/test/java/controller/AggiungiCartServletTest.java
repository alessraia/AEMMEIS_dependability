package controller;

import controller.utente.AggiungiCartServlet;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.*;

public class AggiungiCartServletTest {

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreXYZ");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        new AggiungiCartServlet().doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void addExistingBook_incrementsQuantity_andForwardsToSource() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        // Setup carrello with one riga for libro
        Libro libroInCart = new Libro();
        libroInCart.setIsbn("ABC-1");

        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libroInCart);
        riga.setQuantita(1);
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);
        carrello.setIdCarrello("cart-1");

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("ABC-1");
        when(request.getParameter("source")).thenReturn("mostraLibro");
        when(request.getRequestDispatcher("mostra-libro")).thenReturn(dispatcher);

        // Mock LibroDAO to return a Libro with same ISBN
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("ABC-1");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ABC-1")).thenReturn(daoLibro))) {

            new AggiungiCartServlet().doGet(request, response);

            // quantity should have been incremented
            assertEquals(2, carrello.getRigheCarrello().get(0).getQuantita());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void addNewBook_addsRiga_andForwardsToComputedAddress() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart-2");
        carrello.setRigheCarrello(new ArrayList<>());

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("NEW-123");
        when(request.getParameter("source")).thenReturn("aggiungi-carrello");
        when(request.getRequestDispatcher("mostra-reparto")).thenReturn(dispatcher);

        // Mock DAO to return the Libro
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("NEW-123");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("NEW-123")).thenReturn(daoLibro))) {

            new AggiungiCartServlet().doGet(request, response);

            // a new riga should be present
            assertEquals(1, carrello.getRigheCarrello().size());
            RigaCarrello added = carrello.getRigheCarrello().get(0);
            assertEquals("NEW-123", added.getLibro().getIsbn());
            assertEquals(1, added.getQuantita());
            assertEquals("cart-2", added.getIdCarrello()); // Verify setIdCarrello was called (kills line 70 mutation)
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void addingBookWithMultipleExistingBooks_incrementsCorrectBook() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        // Setup carrello with 2 righe - add the target book as the SECOND item
        Libro libro1 = new Libro();
        libro1.setIsbn("BOOK-1");
        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        Libro libro2 = new Libro();
        libro2.setIsbn("BOOK-2");
        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);
        riga2.setQuantita(3);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);
        carrello.setIdCarrello("cart-3");

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("BOOK-2");
        when(request.getParameter("source")).thenReturn("mostraLibro");
        when(request.getRequestDispatcher("mostra-libro")).thenReturn(dispatcher);

        // Mock DAO to return libro2
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("BOOK-2");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("BOOK-2")).thenReturn(daoLibro))) {

            new AggiungiCartServlet().doGet(request, response);

            // First book should remain unchanged
            assertEquals(1, carrello.getRigheCarrello().get(0).getQuantita());
            // Second book (at index 1) should be incremented to 4
            assertEquals(4, carrello.getRigheCarrello().get(1).getQuantita());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void sessionAttributeIsUpdatedAfterAddingToCart() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart-4");
        carrello.setRigheCarrello(new ArrayList<>());

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("ISBN-999");
        when(request.getParameter("source")).thenReturn("mostraLibro");
        when(request.getRequestDispatcher("mostra-libro")).thenReturn(dispatcher);

        Libro daoLibro = new Libro();
        daoLibro.setIsbn("ISBN-999");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ISBN-999")).thenReturn(daoLibro))) {

            new AggiungiCartServlet().doGet(request, response);

            // Verify session.setAttribute was called with the updated carrello (kills line 77 mutation)
            verify(session, times(1)).setAttribute("carrello", carrello);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void addNewBookToCartWithExistingDifferentBooks_checksBoundary() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        // Setup carrello with 2 existing books that DON'T match the new one
        // This forces loop to iterate through ALL items without early exit
        Libro libro1 = new Libro();
        libro1.setIsbn("EXISTING-1");
        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(2);

        Libro libro2 = new Libro();
        libro2.setIsbn("EXISTING-2");
        RigaCarrello riga2 = new RigaCarrello();
        riga2.setLibro(libro2);
        riga2.setQuantita(1);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);
        righe.add(riga2);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);
        carrello.setIdCarrello("cart-boundary");

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("NEW-BOOK");
        when(request.getParameter("source")).thenReturn("mostraLibro");
        when(request.getRequestDispatcher("mostra-libro")).thenReturn(dispatcher);

        // Mock DAO to return a NEW book (not in cart)
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("NEW-BOOK");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("NEW-BOOK")).thenReturn(daoLibro))) {

            new AggiungiCartServlet().doGet(request, response);

            // Existing books should remain unchanged
            assertEquals(2, carrello.getRigheCarrello().get(0).getQuantita());
            assertEquals(1, carrello.getRigheCarrello().get(1).getQuantita());
            // New book should be added as third item
            assertEquals(3, carrello.getRigheCarrello().size());
            assertEquals("NEW-BOOK", carrello.getRigheCarrello().get(2).getLibro().getIsbn());
            assertEquals(1, carrello.getRigheCarrello().get(2).getQuantita());
            
            verify(dispatcher, times(1)).forward(request, response);
        }
    }
}
