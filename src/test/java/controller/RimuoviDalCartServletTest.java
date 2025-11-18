package controller;

import controller.utente.RimuoviDalCartServlet;
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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.mockito.Mockito.*;

public class RimuoviDalCartServletTest {

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreSomething");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        new RimuoviDalCartServlet().doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void removeExistingBook_returnsSuccessTrue() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        // Create the libro that is present in the cart
        Libro libroInCart = new Libro();
        libroInCart.setIsbn("111-AAA");

        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libroInCart);
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("111-AAA");

        // Capture response output
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // Mock construction of LibroDAO so doRetrieveById returns a Libro with same ISBN
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("111-AAA");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("111-AAA")).thenReturn(daoLibro))) {

            new RimuoviDalCartServlet().doGet(request, response);

            pw.flush();
            String output = sw.toString();
            assertTrue(output.contains("\"success\":true"));
        }
    }

    @Test
    public void removeNonExistingBook_returnsSuccessFalse() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        // Create the libro that is present in the cart
        Libro libroInCart = new Libro();
        libroInCart.setIsbn("222-BBB");

        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libroInCart);
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(request.getParameter("isbn")).thenReturn("999-XXX");

        // Capture response output
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // Mock construction of LibroDAO so doRetrieveById returns a different Libro
        Libro daoLibro = new Libro();
        daoLibro.setIsbn("999-XXX");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.doRetrieveById("999-XXX")).thenReturn(daoLibro))) {

            new RimuoviDalCartServlet().doGet(request, response);

            pw.flush();
            String output = sw.toString();
            // The cart contains 222-BBB while DAO returned 999-XXX => success should be false
            assertTrue(output.contains("\"success\":false"));
        }
    }
}
