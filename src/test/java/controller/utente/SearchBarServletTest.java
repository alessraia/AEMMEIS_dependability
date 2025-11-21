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
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

class SearchBarServletTest {
    private SearchBarServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private LibroDAO libroDAOMock;
    private Utente utenteMock;

    @BeforeEach
    void setUp() {
        servletUnderTest = new SearchBarServlet();
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
    void testDoGet_SearchReturnsJson() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("keyword");
        // prepare mock results
        Libro l1 = mock(Libro.class);
        when(l1.getIsbn()).thenReturn("isbn1");
        when(l1.getTitolo()).thenReturn("titolo1");
        when(libroDAOMock.Search("keyword")).thenReturn(List.of(l1));

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doGet(request, response);

        pw.flush();
        String out = sw.toString();
        assertTrue(out.contains("isbn1"));
        assertTrue(out.contains("titolo1"));
        verify(response).setContentType("application/json");
        verify(response).setCharacterEncoding("UTF-8");
    }

    @Test
    void testDoGet_EmptyQueryReturnsEmptyJsonArray() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("");
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doGet(request, response);

        pw.flush();
        String out = sw.toString();
        assertEquals("[]", out.trim());
    }
}
