package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

class RicercaServletTest {
    private RicercaServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private LibroDAO libroDAOMock;
    private Utente utenteMock;

    @BeforeEach
    void setUp() {
        servletUnderTest = new RicercaServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        libroDAOMock = mock(LibroDAO.class);
        utenteMock = mock(Utente.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(utenteMock.getTipo()).thenReturn("");

        servletUnderTest.setLibroDAO(libroDAOMock);
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        when(utenteMock.getTipo()).thenReturn("Gestore");
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_SearchWithResults_ForwardsAndSetsAttributes() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("keyword");
        Libro l1 = mock(Libro.class);
        when(l1.getIsbn()).thenReturn("isbn1");
        when(l1.getTitolo()).thenReturn("titolo1");
        when(libroDAOMock.Search("keyword")).thenReturn(List.of(l1));

        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/ricerca.jsp")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).setAttribute(eq("results"), any());
        verify(request).setAttribute("q", "keyword");
        verify(request).getRequestDispatcher("/WEB-INF/results/ricerca.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_EmptyQuery_ForwardsToIndex() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("");
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("index.html")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("index.html");
        verify(dispatcher).forward(request, response);
    }
}
